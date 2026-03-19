export type CheckResponse = {
  status: "ok" | "error";
  tag: string | null;
  detail: string | null;
  cause: string | null;
  context: Record<string, string>;
  stage: string | null;
  exit_code: number;
  duration_ms: number;
  logs: string[];
  raw_output: string;
};

export type JobStatusResponse = {
  job_id: string;
  kind: "wf" | "compat";
  state: "queued" | "running" | "succeeded" | "failed";
  stage: string;
  created_at: string;
  updated_at: string;
  finished_at: string | null;
  logs: string[];
  result: CheckResponse | null;
};

const API_BASE_URL = (import.meta.env.VITE_BACKEND_URL as string | undefined) ?? "http://127.0.0.1:8000";

async function parseJsonOrThrow(response: Response): Promise<any> {
  if (!response.ok) {
    const text = await response.text();
    throw new Error(`Backend request failed (${response.status}): ${text}`);
  }
  return response.json();
}

export async function startCompatJob(oldSpecYaml: string, newSpecYaml: string): Promise<{ job_id: string }> {
  const response = await fetch(`${API_BASE_URL}/api/compat/check`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
    },
    body: JSON.stringify({ old_spec_yaml: oldSpecYaml, new_spec_yaml: newSpecYaml }),
  });

  return parseJsonOrThrow(response);
}

export async function getJobStatus(jobId: string): Promise<JobStatusResponse> {
  const response = await fetch(`${API_BASE_URL}/api/jobs/${jobId}`);
  return parseJsonOrThrow(response);
}
