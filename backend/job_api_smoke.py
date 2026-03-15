from __future__ import annotations

import json
import subprocess
import time
import urllib.error
import urllib.request


OLD_SPEC = """openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas: {}
"""

NEW_SPEC = """openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
  /health:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas: {}
"""


def post_json(url: str, payload: dict[str, object]) -> dict[str, object]:
  body = json.dumps(payload).encode("utf-8")
  request = urllib.request.Request(
    url,
    data=body,
    method="POST",
    headers={"Content-Type": "application/json"},
  )
  with urllib.request.urlopen(request) as response:
    return json.loads(response.read())


def get_json(url: str) -> dict[str, object]:
  with urllib.request.urlopen(url) as response:
    return json.loads(response.read())


def wait_for_health(base_url: str, timeout_seconds: int = 20) -> bool:
  deadline = time.time() + timeout_seconds
  while time.time() < deadline:
    try:
      _ = get_json(f"{base_url}/health")
      return True
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError):
      time.sleep(0.25)
  return False


def main() -> int:
  port = 8010
  base_url = f"http://127.0.0.1:{port}"
  server = subprocess.Popen(
    [
      "python",
      "-m",
      "uvicorn",
      "backend.app.main:app",
      "--host",
      "127.0.0.1",
      "--port",
      str(port),
    ],
    cwd="..",
    stdout=subprocess.DEVNULL,
    stderr=subprocess.DEVNULL,
  )

  try:
    if not wait_for_health(base_url):
      print("backend failed to start")
      return 1

    created = post_json(
      f"{base_url}/api/compat/check",
      {"old_spec_yaml": OLD_SPEC, "new_spec_yaml": NEW_SPEC},
    )
    job_id = created.get("job_id")
    if not isinstance(job_id, str) or not job_id:
      print("failed missing job_id")
      return 1

    deadline = time.time() + 60
    while time.time() < deadline:
      status = get_json(f"{base_url}/api/jobs/{job_id}")
      state = status.get("state")
      result = status.get("result")
      if state in {"succeeded", "failed"} and isinstance(result, dict):
        tag = result.get("tag")
        break
      time.sleep(0.5)
    else:
      print("failed timeout waiting for job completion")
      return 1

    if tag == "COMPAT_OK":
      print("succeeded", tag)
      return 0
    print("failed", tag)
    return 1
  finally:
    server.terminate()
    try:
      server.wait(timeout=5)
    except subprocess.TimeoutExpired:
      server.kill()
      server.wait(timeout=5)


if __name__ == "__main__":
    raise SystemExit(main())
