import { useState, useCallback, useRef, useEffect } from "react";
import Header from "@/components/Header";
import YamlPanel from "@/components/YamlPanel";
import ResultDisplay from "@/components/ResultDisplay";
import { oldApiExample, newApiExample } from "@/data/examples";
import { getJobStatus, startCompatJob, type CheckResponse } from "@/lib/api";
import { Loader2 } from "lucide-react";

const Index = () => {
  const [oldApi, setOldApi] = useState("");
  const [newApi, setNewApi] = useState("");
  const [result, setResult] = useState<CheckResponse | null>(null);
  const [computing, setComputing] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const resultRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (result) {
      resultRef.current?.scrollIntoView({ behavior: "smooth", block: "start" });
    }
  }, [result]);

  const handleCompute = useCallback(async () => {
    if (!oldApi.trim() || !newApi.trim()) return;
    setResult(null);
    setError(null);
    setComputing(true);

    try {
      const { job_id: jobId } = await startCompatJob(oldApi, newApi);

      while (true) {
        const status = await getJobStatus(jobId);

        if ((status.state === "succeeded" || status.state === "failed") && status.result) {
          setResult(status.result);
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
            onClear={() => setOldApi("")}
          />
          <YamlPanel
            title="New API"
            subtitle="Candidate"
            value={newApi}
            onChange={setNewApi}
            onLoadExample={() => setNewApi(newApiExample)}
            onClear={() => setNewApi("")}
          />
        </div>

        <div className="mt-8 text-center">
          <button
            onClick={handleCompute}
            disabled={computing || !oldApi.trim() || !newApi.trim()}
            className="inline-flex items-center gap-2 rounded-lg bg-primary px-7 py-2.5 text-sm font-semibold text-primary-foreground shadow-lg shadow-primary/20 transition-all hover:brightness-110 disabled:cursor-not-allowed disabled:opacity-30 disabled:shadow-none"
          >
            {computing && <Loader2 className="h-4 w-4 animate-spin" />}
            {computing ? "Checking…" : "Check Compatibility"}
          </button>
          {error && <p className="mx-auto mt-3 max-w-xl text-xs text-destructive">{error}</p>}
        </div>

        {computing && !result && (
          <div className="mx-auto mt-8 max-w-2xl">
            <div className="animate-pulse rounded-xl border border-border bg-card p-5">
              <div className="h-8 w-36 rounded-md bg-muted" />
              <div className="mt-3 h-4 w-3/4 rounded bg-muted" />
              <div className="mt-2 h-3 w-1/3 rounded bg-muted" />
            </div>
          </div>
        )}
        <div ref={resultRef}>
          <ResultDisplay result={result} />
        </div>
      </main>

      <footer className="border-t border-border py-4 text-center text-[11px] text-muted-foreground">
        Research prototype · Results derived from formal Agda model
      </footer>
    </div>
  );
};

export default Index;
