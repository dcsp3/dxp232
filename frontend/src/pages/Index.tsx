import { useState, useCallback, useRef, useEffect } from "react";
import { useLocation, useNavigate } from "react-router-dom";
import Header from "@/components/Header";
import YamlPanel from "@/components/YamlPanel";
import ResultDisplay from "@/components/ResultDisplay";
import { oldApiExample, newApiExample, EXAMPLES } from "@/data/examples";
import { getJobStatus, startCompatJob, type CheckResponse } from "@/lib/api";
import { ArrowUpDown, BookOpen, Loader2 } from "lucide-react";

const Index = () => {
  const location = useLocation();
  const navigate = useNavigate();

  const [oldApi, setOldApi] = useState<string>(
    () => (location.state as { oldSpec?: string } | null)?.oldSpec ?? ""
  );
  const [newApi, setNewApi] = useState<string>(
    () => (location.state as { newSpec?: string } | null)?.newSpec ?? ""
  );
  const [result, setResult] = useState<CheckResponse | null>(null);
  const [computing, setComputing] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [elapsedSeconds, setElapsedSeconds] = useState(0);
  const resultRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (result) {
      resultRef.current?.scrollIntoView({ behavior: "smooth", block: "start" });
    }
  }, [result]);

  useEffect(() => {
    if (!computing) {
      setElapsedSeconds(0);
      return;
    }

    const interval = window.setInterval(() => {
      setElapsedSeconds((current) => current + 1);
    }, 1000);

    return () => window.clearInterval(interval);
  }, [computing]);

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

  const handleSwap = useCallback(() => {
    setOldApi(newApi);
    setNewApi(oldApi);
    setResult(null);
    setError(null);
  }, [newApi, oldApi]);

  const fromExampleId = (location.state as { fromExample?: string } | null)?.fromExample;
  const loadedExampleTitle = fromExampleId
    ? (EXAMPLES.find((e) => e.id === fromExampleId)?.title ?? null)
    : null;

  return (
    <div className="flex min-h-screen flex-col bg-background">
      <Header />

      <main className="mx-auto w-full max-w-5xl flex-1 px-6 py-8">
        {loadedExampleTitle && (
          <div className="mb-4 flex items-center gap-2 rounded-lg border border-border bg-card/80 px-4 py-2.5">
            <BookOpen className="h-3.5 w-3.5 shrink-0 text-muted-foreground" />
            <p className="text-xs text-muted-foreground">
              Example loaded:{" "}
              <span className="font-medium text-foreground">{loadedExampleTitle}</span>
            </p>
            <button
              onClick={() => navigate("/examples")}
              className="ml-auto text-xs text-muted-foreground underline-offset-2 hover:text-foreground hover:underline"
            >
              Browse all
            </button>
          </div>
        )}
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
          <div className="flex flex-wrap items-center justify-center gap-3">
            <button
              onClick={handleCompute}
              disabled={computing || !oldApi.trim() || !newApi.trim()}
              className="inline-flex items-center gap-2 rounded-lg bg-primary px-7 py-2.5 text-sm font-semibold text-primary-foreground shadow-lg shadow-primary/20 transition-all hover:brightness-110 disabled:cursor-not-allowed disabled:opacity-30 disabled:shadow-none"
            >
              {computing && <Loader2 className="h-4 w-4 animate-spin" />}
              {computing ? "Checking…" : "Check Compatibility"}
            </button>
            <button
              onClick={handleSwap}
              disabled={computing || (!oldApi.trim() && !newApi.trim())}
              className="inline-flex items-center gap-2 rounded-lg border border-border bg-card px-4 py-2.5 text-sm font-medium text-foreground transition-colors hover:bg-muted disabled:cursor-not-allowed disabled:opacity-40"
            >
              <ArrowUpDown className="h-4 w-4" />
              Swap Old / New
            </button>
          </div>
          {computing && (
            <p className="mt-3 text-xs text-muted-foreground">
              Running compatibility check... {elapsedSeconds}s elapsed
            </p>
          )}
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
        {!computing && !result && !error && (
          <div className="mx-auto mt-8 max-w-2xl rounded-xl border border-dashed border-border bg-card/60 p-6 text-left">
            <p className="text-sm font-semibold text-foreground">How to use</p>
            <p className="mt-2 text-sm text-muted-foreground">
              Paste an older and newer OpenAPI spec, then run a check to get a compatibility verdict,
              a short diagnosis, and structured details about any breaking change.
            </p>
            <button
              onClick={() => navigate("/examples")}
              className="mt-4 inline-flex items-center gap-1.5 rounded-md border border-border bg-background px-3 py-1.5 text-xs font-medium text-foreground transition-colors hover:bg-muted"
            >
              <BookOpen className="h-3.5 w-3.5" />
              Browse example pairs
            </button>
          </div>
        )}
        <div ref={resultRef}>
          <ResultDisplay result={result} />
        </div>
      </main>

      <footer className="border-t border-border py-4 text-center text-[11px] text-muted-foreground">
        Compatibility results derived from a formal Agda model
      </footer>
    </div>
  );
};

export default Index;
