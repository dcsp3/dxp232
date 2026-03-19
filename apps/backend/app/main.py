from __future__ import annotations

import asyncio
import shutil
import time
from typing import Any

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware

from .job_store import JobStore
from .parser_runner import ParserRunner, infer_stage_from_line
from .schemas import (
    CheckResponse,
    CompatCheckRequest,
    HealthResponse,
    JobCreateResponse,
    JobStatusResponse,
)
from .settings import load_settings

settings = load_settings()
runner = ParserRunner(settings=settings)
job_store = JobStore(max_log_lines_per_job=settings.max_log_lines_per_job)
_background_tasks: set[asyncio.Task[Any]] = set()

app = FastAPI(
    title="Compatibility Checker API",
    version="1.0.0",
    description="HTTP API for WF and compatibility checks over OpenAPI YAML specs.",
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=list(settings.cors_allow_origins),
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.get("/health", response_model=HealthResponse)
def health() -> HealthResponse:
    return HealthResponse(
        status="ok",
        parser_cli_exists=settings.parser_cli_path.exists(),
        parser_dir_exists=settings.parser_dir.exists(),
        agda_in_path=shutil.which("agda") is not None,
    )


@app.post("/api/compat/check", response_model=JobCreateResponse)
async def start_compat_job(request: CompatCheckRequest) -> JobCreateResponse:
    job = job_store.create_job("compat")
    job_store.set_running(job.job_id, stage="starting")
    _schedule_background_job(_run_compat_job(job.job_id, request.old_spec_yaml, request.new_spec_yaml))
    return JobCreateResponse(
        job_id=job.job_id,
        kind=job.kind,
        state="running",
        stage="starting",
        created_at=job.created_at,
    )


@app.get("/api/jobs/{job_id}", response_model=JobStatusResponse)
def get_job(job_id: str) -> JobStatusResponse:
    job = job_store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")

    return JobStatusResponse(
        job_id=job.job_id,
        kind=job.kind,
        state=job.state,
        stage=job.stage,
        created_at=job.created_at,
        updated_at=job.updated_at,
        finished_at=job.finished_at,
        logs=job.logs,
        result=job.result,
    )


async def _run_compat_job(job_id: str, old_spec_yaml: str, new_spec_yaml: str) -> None:
    started = time.perf_counter()

    def on_line(line: str) -> None:
        job_store.append_log(job_id, line)
        stage = infer_stage_from_line(line)
        if stage:
            job_store.update_stage(job_id, stage)

    try:
        result = await runner.run_compat(old_spec_yaml, new_spec_yaml, on_line=on_line)
        result.duration_ms = int((time.perf_counter() - started) * 1000)
        job_store.complete(job_id, result)
    except Exception as error:
        error_text = f"{error.__class__.__name__}: {error}" if str(error) else error.__class__.__name__
        message = f"BACKEND_ERROR:COMPAT_JOB_FAILED: {error_text}"
        job_store.append_log(job_id, message)
        job_store.complete(
            job_id,
            CheckResponse(
                status="error",
                tag="BACKEND_ERROR:COMPAT_JOB_FAILED",
                detail=error_text,
                context={},
                stage="failed",
                exit_code=3,
                duration_ms=int((time.perf_counter() - started) * 1000),
                logs=[message],
                raw_output=message,
            ),
        )


def _schedule_background_job(coro: Any) -> None:
    task = asyncio.create_task(coro)
    _background_tasks.add(task)

    def _cleanup(done_task: asyncio.Task[Any]) -> None:
        _background_tasks.discard(done_task)

    task.add_done_callback(_cleanup)
