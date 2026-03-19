from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Settings:
    repo_root: Path
    parser_dir: Path
    parser_cli_path: Path
    python_executable: str
    command_timeout_seconds: int
    max_log_lines_per_job: int
    cors_allow_origins: tuple[str, ...] 


def load_settings() -> Settings:
    repo_root = Path(__file__).resolve().parents[3]
    parser_dir = repo_root / "parser"
    parser_cli_path = parser_dir / "cli.py"

    timeout_raw = os.getenv("BACKEND_COMMAND_TIMEOUT_SECONDS", "600")
    logs_raw = os.getenv("BACKEND_MAX_LOG_LINES_PER_JOB", "400")
    cors_raw = os.getenv("BACKEND_CORS_ALLOW_ORIGINS", "*")

    timeout_seconds = max(30, int(timeout_raw))
    max_log_lines = max(50, int(logs_raw))
    cors_allow_origins = tuple(origin.strip() for origin in cors_raw.split(",") if origin.strip())
    if not cors_allow_origins:
        cors_allow_origins = ("*",)

    return Settings(
        repo_root=repo_root,
        parser_dir=parser_dir,
        parser_cli_path=parser_cli_path,
        python_executable=sys.executable,
        command_timeout_seconds=timeout_seconds,
        max_log_lines_per_job=max_log_lines,
        cors_allow_origins=cors_allow_origins,
    )
