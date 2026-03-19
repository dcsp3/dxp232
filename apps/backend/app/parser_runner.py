from __future__ import annotations

import asyncio
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from .schemas import CheckResponse
from .settings import Settings


TAG_PREFIXES = (
    "WF_OK",
    "WF_ERR:",
    "TRANSLATION_ERR:",
    "WF_CHECK_ERROR:",
    "COMPAT_OK",
    "COMPAT_ERR:",
    "COMPAT_CHECK_ERROR:",
)


def parse_context_line(context_line: str) -> dict[str, str]:
    payload = context_line[len("CONTEXT:") :].strip()
    context: dict[str, str] = {}
    if not payload:
        return context

    for item in payload.split(" "):
        if not item or "=" not in item:
            continue
        key, value = item.split("=", 1)
        if key and value:
            context[key] = value

    return context


def infer_stage_from_line(line: str) -> str | None:
    if line.startswith("Generated "):
        return "generating"
    if line == "WF_CHECK: old spec":
        return "wf_old_check"
    if line == "WF_CHECK: new spec":
        return "wf_new_check"
    if line.startswith("WF_OK:"):
        return "wf_passed"
    if line == "COMPAT_CHECK: old -> new":
        return "compat_check"
    if line.startswith(TAG_PREFIXES):
        return "completed"
    return None


@dataclass
class ParserRunner:
    settings: Settings

    async def run_compat(
        self,
        old_spec_yaml: str,
        new_spec_yaml: str,
        on_line: Callable[[str], None] | None = None,
    ) -> CheckResponse:
        with tempfile.TemporaryDirectory(prefix="dxp-compat-") as temp_dir_raw:
            temp_dir = Path(temp_dir_raw)
            old_spec_path = temp_dir / "old.yaml"
            new_spec_path = temp_dir / "new.yaml"
            old_spec_path.write_text(old_spec_yaml, encoding="utf-8")
            new_spec_path.write_text(new_spec_yaml, encoding="utf-8")

            cmd = [
                self.settings.python_executable,
                str(self.settings.parser_cli_path),
                "check-compat",
                str(old_spec_path),
                str(new_spec_path),
            ]
            return await self._run_command(cmd, on_line=on_line)

    async def _run_command(
        self,
        cmd: list[str],
        on_line: Callable[[str], None] | None = None,
    ) -> CheckResponse:
        return await asyncio.to_thread(self._run_command_sync, cmd, on_line)

    def _run_command_sync(
        self,
        cmd: list[str],
        on_line: Callable[[str], None] | None = None,
    ) -> CheckResponse:
        try:
            completed = subprocess.run(
                cmd,
                cwd=str(self.settings.parser_dir),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=self.settings.command_timeout_seconds,
            )
        except subprocess.TimeoutExpired as error:
            partial_output = error.output or ""
            if isinstance(partial_output, bytes):
                partial_output = partial_output.decode("utf-8", errors="replace")
            lines = [line.rstrip("\r\n") for line in str(partial_output).splitlines()]
            timeout_line = f"BACKEND_ERROR:COMMAND_TIMEOUT ({self.settings.command_timeout_seconds}s)"
            lines.append(timeout_line)
            if on_line:
                for line in lines:
                    on_line(line)
            return CheckResponse(
                status="error",
                tag="BACKEND_ERROR:COMMAND_TIMEOUT",
                detail=f"Parser command timed out after {self.settings.command_timeout_seconds} seconds.",
                context={},
                stage="timeout",
                exit_code=124,
                duration_ms=self.settings.command_timeout_seconds * 1000,
                logs=lines,
                raw_output="\n".join(lines),
            )

        output = completed.stdout or ""
        lines = [line.rstrip("\r\n") for line in output.splitlines()]
        if on_line:
            for line in lines:
                on_line(line)

        return build_check_response(lines, completed.returncode)


def build_check_response(lines: list[str], exit_code: int) -> CheckResponse:
    tag: str | None = None
    detail: str | None = None
    cause: str | None = None
    context: dict[str, str] = {}
    last_stage: str | None = None
    detail_lines: list[str] = []

    in_details_block = False
    details_block: list[str] = []

    for line in lines:
        stage = infer_stage_from_line(line)
        if stage:
            last_stage = stage

        if line.startswith(TAG_PREFIXES):
            tag = line.strip()

        if line.startswith("DETAIL:"):
            detail_lines.append(line[len("DETAIL:") :].strip())

        if line.startswith("CAUSE:") and cause is None:
            cause = line[len("CAUSE:") :].strip()

        if line.startswith("CONTEXT:"):
            context = parse_context_line(line)

        if line == "DETAILS_START":
            in_details_block = True
            continue
        if line == "DETAILS_END":
            in_details_block = False
            continue
        if in_details_block:
            details_block.append(line)

    if detail_lines:
        detail = "\n".join(part for part in detail_lines if part).strip() or None
    if detail is None and details_block:
        detail = "\n".join(details_block).strip() or None

    status = "error"
    if tag in {"WF_OK", "COMPAT_OK"}:
        status = "ok"
    elif tag is None and exit_code == 0:
        status = "ok"

    if last_stage is None:
        last_stage = "completed"

    return CheckResponse(
        status=status,
        tag=tag,
        detail=detail,
        cause=cause,
        context=context,
        stage=last_stage,
        exit_code=exit_code,
        duration_ms=0,
        logs=lines,
        raw_output="\n".join(lines),
    )
