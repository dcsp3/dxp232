# Backend 

FastAPI wrapper around the parser CLI for WF and compatibility checks.

## Run

From repository root:

```powershell
python -m pip install -r backend/requirements.txt
python -m uvicorn backend.app.main:app --host 127.0.0.1 --port 8000 --reload
```

Open docs:
- http://127.0.0.1:8000/docs

## Endpoints

- `GET /health`
- `POST /api/compat/check`
- `GET /api/jobs/{job_id}`

Primary API is jobs-first:
- `POST /api/compat/check` enqueues a compatibility check and returns `job_id`.
- Poll `GET /api/jobs/{job_id}` for status/logs/result.

Compat:

```json
{
  "old_spec_yaml": "openapi: 3.1.0\npaths: {}\ncomponents:\n  schemas: {}\n",
  "new_spec_yaml": "openapi: 3.1.0\npaths: {}\ncomponents:\n  schemas: {}\n"
}
```

## Notes

- The backend reuses `parser/cli.py` via subprocess, so existing parser behavior remains the source of truth.
- Jobs API supports polling for progress and logs while checks run.
- Ensure agda is installed and available in PATH on the machine running this backend.
