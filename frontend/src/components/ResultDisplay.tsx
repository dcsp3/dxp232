import { CheckCircle2, XCircle, ChevronDown, ChevronRight, Copy, Check } from "lucide-react";
import { useState } from "react";
import type { CheckResponse } from "@/lib/api";

interface ResultDisplayProps {
  result: CheckResponse | null;
}

function classifyTag(tag: string | null): string {
  if (!tag) return "Unknown";
  if (tag === "COMPAT_OK") return "Compatible";
  if (tag.startsWith("TRANSLATION_ERROR")) return "Input Error";
  if (tag.startsWith("WF_ERR")) return "Well-Formedness Error";
  if (tag.startsWith("COMPAT_ERR")) return "Compatibility Drift";
  if (tag.startsWith("BACKEND_ERROR")) return "Internal Error";
  return "Error";
}

function describeTag(tag: string | null): string {
  if (!tag) return "No result tag was returned by the backend.";

  switch (tag) {
    case "COMPAT_OK":
      return "APIs are compatible. The old API is a refinement of the new one.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_SHAPE_MISMATCH":
      return "A shared component schema changed structural shape between versions.";
    case "COMPAT_ERR:ENDPOINT_REMOVED":
      return "An endpoint present in the old API is missing in the new API.";
    default:
      if (tag.startsWith("TRANSLATION_ERROR")) {
        return "The YAML could not be translated into the supported OpenAPI subset.";
      }
      if (tag.startsWith("WF_ERR")) {
        return "The specification failed formal well-formedness checks.";
      }
      if (tag.startsWith("COMPAT_ERR")) {
        return "The APIs are not compatible under the formal refinement relation.";
      }
      if (tag.startsWith("BACKEND_ERROR")) {
        return "The backend encountered an internal failure while running the check.";
      }
      return "Compatibility check returned an unclassified result tag.";
  }
}

function labelContextKey(key: string): string {
  const keyMap: Record<string, string> = {
    component: "Component",
    endpoint: "Endpoint",
    method: "Method",
    path: "Path",
    old_type: "Old Type",
    new_type: "New Type",
    property: "Property",
    response: "Response",
    status: "Status",
  };

  return keyMap[key] ?? key;
}

const ResultDisplay = ({ result }: ResultDisplayProps) => {
  const [detailsOpen, setDetailsOpen] = useState(false);
  const [logsOpen, setLogsOpen] = useState(false);
  const [copiedKey, setCopiedKey] = useState<string | null>(null);

  if (!result) return null;

  const isCompatible = result.tag === "COMPAT_OK";
  const summary = describeTag(result.tag);
  const allContextEntries = Object.entries(result.context ?? {});
  
  // Reorder context to prioritize path for endpoint errors
  const contextEntries = result.tag?.startsWith("COMPAT_ERR:ENDPOINT")
    ? [...allContextEntries.filter(([k]) => k === "path"), ...allContextEntries.filter(([k]) => k !== "path")]
    : allContextEntries;
  
  const summaryText = [
    `Tag: ${result.tag ?? "(none)"}`,
    contextEntries.map(([key, value]) => `${labelContextKey(key)}: ${value}`).join(", "),
  ]
    .filter(Boolean)
    .join("\n");

  const handleCopy = async (text: string, key: string) => {
    try {
      await navigator.clipboard.writeText(text);
      setCopiedKey(key);
      setTimeout(() => setCopiedKey(null), 1800);
    } catch {
      // clipboard not available
    }
  };

  return (
    <div className="mx-auto mt-8 max-w-2xl text-left">
      <div className="rounded-xl border border-border bg-card p-5 shadow-sm">
        {isCompatible ? (
          <div className="inline-flex items-center gap-2.5 rounded-md border border-success/30 bg-success/10 px-4 py-2.5">
            <CheckCircle2 className="h-5 w-5 text-success" />
            <span className="text-sm font-semibold text-success">Compatible</span>
          </div>
        ) : (
          <div className="inline-flex items-center gap-2.5 rounded-md border border-destructive/30 bg-destructive/10 px-4 py-2.5">
            <XCircle className="h-5 w-5 text-destructive" />
            <span className="text-sm font-semibold text-destructive">Incompatible</span>
          </div>
        )}

        <p className="mt-3 text-sm font-medium text-foreground">{summary}</p>

        {result.tag && (
          <p className="mt-2 text-xs text-muted-foreground">
            Tag: <span className="font-mono text-foreground">{result.tag}</span>
          </p>
        )}

        <div className="mt-4 flex flex-wrap gap-2">
          <button
            onClick={() => handleCopy(summaryText, "summary")}
            className="inline-flex items-center gap-1 rounded-md border border-border bg-background px-2.5 py-1.5 text-xs font-medium text-foreground transition-colors hover:bg-muted"
          >
            {copiedKey === "summary" ? <Check className="h-3.5 w-3.5 text-success" /> : <Copy className="h-3.5 w-3.5" />}
            {copiedKey === "summary" ? "Copied!" : "Copy Summary"}
          </button>
          {result.logs.length > 0 && (
            <button
              onClick={() => handleCopy(result.logs.join("\n"), "logs")}
              className="inline-flex items-center gap-1 rounded-md border border-border bg-background px-2.5 py-1.5 text-xs font-medium text-foreground transition-colors hover:bg-muted"
            >
              {copiedKey === "logs" ? <Check className="h-3.5 w-3.5 text-success" /> : <Copy className="h-3.5 w-3.5" />}
              {copiedKey === "logs" ? "Copied!" : "Copy Logs"}
            </button>
          )}
        </div>

        <div className="mt-4">
          <button
            onClick={() => setDetailsOpen(!detailsOpen)}
            className="inline-flex items-center gap-1 text-xs font-medium text-muted-foreground transition-colors hover:text-foreground"
          >
            {detailsOpen ? <ChevronDown className="h-3.5 w-3.5" /> : <ChevronRight className="h-3.5 w-3.5" />}
            Details
          </button>
          {detailsOpen && (
            <div className="mt-3 rounded-md border border-border bg-muted/50 px-4 py-3 text-xs text-muted-foreground">
              {result.detail && <p className="whitespace-pre-wrap">{result.detail}</p>}
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
                        className="rounded border border-border bg-card px-2 py-1 text-[11px] text-foreground"
                        title={key}
                      >
                        <span className="font-medium">{labelContextKey(key)}:</span> <span className="font-mono">{value}</span>
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
    </div>
  );
};

export default ResultDisplay;
