# Frontend

Vite + React frontend for compatibility checking against the local FastAPI backend.

## What This UI Does

- accepts pasted YAML for old/new OpenAPI specs
- starts backend compatibility jobs
- polls job status for stage updates
- displays final compatibility tag, detail, context, and logs

## Prerequisites

- Node.js 18+
- backend server running from this repository

## Run

From this folder:

```powershell
npm install
$env:VITE_BACKEND_URL="http://127.0.0.1:8000"
npm run dev
```

## Build/Test

```powershell
npm run build
npm run test
```

## Backend Dependency

This frontend expects backend routes:

- `POST /api/compat/check`
- `GET /api/jobs/{job_id}`

If backend is not reachable, UI displays request errors in the result area.
