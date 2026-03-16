from __future__ import annotations

from datetime import datetime
from typing import Literal

from pydantic import BaseModel, Field


class CompatCheckRequest(BaseModel):
    old_spec_yaml: str = Field(min_length=1)
    new_spec_yaml: str = Field(min_length=1)


class CheckResponse(BaseModel):
    status: Literal["ok", "error"]
    tag: str | None = None
    detail: str | None = None
    cause: str | None = None
    context: dict[str, str] = Field(default_factory=dict)
    stage: str | None = None
    exit_code: int
    duration_ms: int
    logs: list[str] = Field(default_factory=list)
    raw_output: str = ""


class JobCreateResponse(BaseModel):
    job_id: str
    kind: Literal["compat"]
    state: Literal["queued", "running", "succeeded", "failed"]
    stage: str
    created_at: datetime


class JobStatusResponse(BaseModel):
    job_id: str
    kind: Literal["compat"]
    state: Literal["queued", "running", "succeeded", "failed"]
    stage: str
    created_at: datetime
    updated_at: datetime
    finished_at: datetime | None = None
    logs: list[str] = Field(default_factory=list)
    result: CheckResponse | None = None


class HealthResponse(BaseModel):
    status: Literal["ok"]
    parser_cli_exists: bool
    parser_dir_exists: bool
    agda_in_path: bool
