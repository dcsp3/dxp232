import { useState, useCallback } from "react";
import Header from "@/components/Header";
import YamlPanel from "@/components/YamlPanel";
import ProgressSteps from "@/components/ProgressSteps";
import ResultDisplay from "@/components/ResultDisplay";
import { oldApiExample, newApiExample } from "@/data/examples";
import { getJobStatus, startCompatJob, type CheckResponse } from "@/lib/api";

const STAGE_TO_STEP: Record<string, number> = {
  queued: 0,
  starting: 0,
  generating: 1,
  wf_old_check: 2,
  wf_new_check: 3,
  compat_check: 4,
  completed: 5,
};

const STEPS = [
  "Job queued",
  "Generating Agda modules",
  "WF check (old)",
  "WF check (new)",
  "Compatibility check",
  "Completed",
];

const Index = () => {
  const [oldApi, setOldApi] = useState("");
  const [newApi, setNewApi] = useState("");
  const [step, setStep] = useState(-1);
  const [result, setResult] = useState<CheckResponse | null>(null);
  const [computing, setComputing] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [completed, setCompleted] = useState(false);

  const handleCompute = useCallback(async () => {
    if (!oldApi.trim() || !newApi.trim()) return;
    setResult(null);
    setError(null);
    setComputing(true);
    setStep(0);
    setCompleted(false);

    try {
      const { job_id: jobId } = await startCompatJob(oldApi, newApi);

      while (true) {
        const status = await getJobStatus(jobId);
        const mappedStep = STAGE_TO_STEP[status.stage] ?? (status.state === "queued" ? 0 : 1);
        setStep(mappedStep);

        if ((status.state === "succeeded" || status.state === "failed") && status.result) {
          setResult(status.result);
          setCompleted(true);
          setComputing(false);
          return;
        }

        await new Promise((resolve) => setTimeout(resolve, 1500));
      }
    } catch (err) {
      const message = err instanceof Error ? err.message : "Compatibility check failed.";
      setError(message);
      setComputing(false);
    }
  }, [oldApi, newApi]);

  return (
    <div className="flex min-h-screen flex-col bg-background">
      <Header />

      <main className="mx-auto w-full max-w-5xl flex-1 px-6 py-8">
        <div className="flex flex-col gap-3 md:flex-row">
          <YamlPanel
            title="Old API"
            subtitle="Baseline"
            value={oldApi}
            onChange={setOldApi}
            onLoadExample={() => setOldApi(oldApiExample)}
          />
          <YamlPanel
            title="New API"
            subtitle="Candidate"
            value={newApi}
            onChange={setNewApi}
            onLoadExample={() => setNewApi(newApiExample)}
          />
        </div>

        <div className="mt-8 text-center">
          <button
            onClick={handleCompute}
            disabled={computing || !oldApi.trim() || !newApi.trim()}
            className="rounded-lg bg-primary px-7 py-2.5 text-sm font-semibold text-primary-foreground shadow-lg shadow-primary/20 transition-all hover:brightness-110 disabled:cursor-not-allowed disabled:opacity-30 disabled:shadow-none"
          >
            {computing ? "Computing…" : "Compute Refinement"}
          </button>

          <ProgressSteps currentStep={step} steps={STEPS} completed={completed} />
          {error && <p className="mx-auto mt-3 max-w-xl text-xs text-destructive">{error}</p>}
        </div>

        <ResultDisplay result={result} />
      </main>

      <footer className="border-t border-border py-4 text-center text-[11px] text-muted-foreground">
        Research prototype · Results derived from formal Agda model
      </footer>
    </div>
  );
};

export default Index;
