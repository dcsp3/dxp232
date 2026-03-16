import { CheckCircle2, XCircle, ChevronDown, ChevronRight } from "lucide-react";
import { useState } from "react";
import type { CheckResponse } from "@/lib/api";

interface ResultDisplayProps {
  result: CheckResponse | null;
}

const ResultDisplay = ({ result }: ResultDisplayProps) => {
  const [detailsOpen, setDetailsOpen] = useState(false);
  const [logsOpen, setLogsOpen] = useState(false);

  if (!result) return null;

  const isCompatible = result.tag === "COMPAT_OK";
  const contextEntries = Object.entries(result.context ?? {});

  return (
    <div className="mx-auto mt-8 max-w-md text-center">
      {isCompatible ? (
        <div className="inline-flex items-center gap-2.5 rounded-md border border-success/30 bg-success/10 px-5 py-3">
          <CheckCircle2 className="h-5 w-5 text-success" />
          <span className="text-sm font-semibold text-success">Compatible</span>
        </div>
      ) : (
        <div className="inline-flex items-center gap-2.5 rounded-md border border-destructive/30 bg-destructive/10 px-5 py-3">
          <XCircle className="h-5 w-5 text-destructive" />
          <span className="text-sm font-semibold text-destructive">Incompatible</span>
        </div>
      )}

      <div className="mt-4">
        <button
          onClick={() => setDetailsOpen(!detailsOpen)}
          className="inline-flex items-center gap-1 text-xs font-medium text-muted-foreground transition-colors hover:text-foreground"
        >
          {detailsOpen ? <ChevronDown className="h-3.5 w-3.5" /> : <ChevronRight className="h-3.5 w-3.5" />}
          Details
        </button>
        {detailsOpen && (
          <div className="mt-3 rounded-md border border-border bg-muted/50 px-4 py-3 text-left text-xs text-muted-foreground">
            <p>
              <span className="font-medium text-foreground">Direction checked:</span> Old ⊑ New
            </p>
            {result.tag && (
              <p className="mt-2">
                <span className="font-medium text-foreground">Tag:</span> {result.tag}
              </p>
            )}
            {result.detail && <p className="mt-2 whitespace-pre-wrap">{result.detail}</p>}
            {result.cause && (
              <p className="mt-2">
                <span className="font-medium text-foreground">Cause:</span> {result.cause}
              </p>
            )}
            {contextEntries.length > 0 && (
              <div className="mt-3">
                <p className="mb-1.5 font-medium text-foreground">Context:</p>
                <div className="flex flex-wrap gap-1.5">
                  {contextEntries.map(([key, value]) => (
                    <span
                      key={`${key}:${value}`}
                      className="rounded border border-border bg-card px-2 py-1 font-mono text-[11px] text-foreground"
                    >
                      {key}={value}
                    </span>
                  ))}
                </div>
              </div>
            )}
            <p className="mt-3 text-[11px] text-muted-foreground">Completed in {result.duration_ms} ms</p>
          </div>
        )}
      </div>

      {result.logs.length > 0 && (
        <div className="mt-4">
          <button
            onClick={() => setLogsOpen(!logsOpen)}
            className="inline-flex items-center gap-1 text-xs font-medium text-muted-foreground transition-colors hover:text-foreground"
          >
            {logsOpen ? <ChevronDown className="h-3.5 w-3.5" /> : <ChevronRight className="h-3.5 w-3.5" />}
            Backend Logs
          </button>
          {logsOpen && (
            <pre className="mt-3 max-h-56 overflow-auto rounded-md border border-border bg-card px-3 py-2 text-left font-mono text-[11px] text-muted-foreground">
              {result.logs.join("\n")}
            </pre>
          )}
        </div>
      )}
    </div>
  );
};

export default ResultDisplay;
