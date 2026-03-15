from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field
from datetime import datetime, timezone
from threading import Lock
from typing import Literal
from uuid import uuid4

from .schemas import CheckResponse

JobKind = Literal["compat"]
JobState = Literal["queued", "running", "succeeded", "failed"]


@dataclass
class JobRecord:
    job_id: str
    kind: JobKind
    state: JobState
    stage: str
    created_at: datetime
    updated_at: datetime
    finished_at: datetime | None = None
    logs: list[str] = field(default_factory=list)
    result: CheckResponse | None = None


class JobStore:
    def __init__(self, max_log_lines_per_job: int = 400) -> None:
        self._jobs: dict[str, JobRecord] = {}
        self._lock = Lock()
        self._max_log_lines_per_job = max_log_lines_per_job

    @staticmethod
    def _now() -> datetime:
        return datetime.now(timezone.utc)

    def create_job(self, kind: JobKind) -> JobRecord:
        now = self._now()
        record = JobRecord(
            job_id=str(uuid4()),
            kind=kind,
            state="queued",
            stage="queued",
            created_at=now,
            updated_at=now,
        )
        with self._lock:
            self._jobs[record.job_id] = record
        return deepcopy(record)

    def set_running(self, job_id: str, stage: str = "starting") -> None:
        with self._lock:
            job = self._jobs[job_id]
            job.state = "running"
            job.stage = stage
            job.updated_at = self._now()

    def update_stage(self, job_id: str, stage: str) -> None:
        with self._lock:
            job = self._jobs[job_id]
            job.stage = stage
            job.updated_at = self._now()

    def append_log(self, job_id: str, line: str) -> None:
        with self._lock:
            job = self._jobs[job_id]
            job.logs.append(line)
            if len(job.logs) > self._max_log_lines_per_job:
                overflow = len(job.logs) - self._max_log_lines_per_job
                del job.logs[:overflow]
            job.updated_at = self._now()

    def complete(self, job_id: str, result: CheckResponse) -> None:
        with self._lock:
            job = self._jobs[job_id]
            job.result = result
            job.finished_at = self._now()
            job.updated_at = job.finished_at
            job.state = "succeeded" if result.status == "ok" else "failed"
            job.stage = "completed"

    def get(self, job_id: str) -> JobRecord | None:
        with self._lock:
            job = self._jobs.get(job_id)
            return deepcopy(job) if job else None
