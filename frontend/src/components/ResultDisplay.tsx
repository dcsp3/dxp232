import { CheckCircle2, XCircle, ChevronDown, ChevronRight, Copy, Check, AlertTriangle, Wrench } from "lucide-react";
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

function buildDiagnosis(result: CheckResponse, contextEntries: Array<[string, string]>): string {
  const context = Object.fromEntries(contextEntries);
  const method = context.method;
  const path = context.path;
  const component = context.component;
  const property = context.property;
  const parameter = context.parameter;
  const oldType = context.old_type;
  const newType = context.new_type;

  if (result.tag === "COMPAT_OK") {
    return "The candidate API preserves the existing contract for the cases checked.";
  }

  if (result.tag === "COMPAT_ERR:ENDPOINT_REMOVED" && method && path) {
    return `${method} ${path} is missing in the candidate API.`;
  }

  if (result.tag?.startsWith("COMPAT_ERR:ENDPOINT_RESPONSE") && method && path) {
    if (oldType && newType) {
      return `${method} ${path} response changed from ${oldType} to ${newType}.`;
    }
    if (oldType) {
      return `${method} ${path} response changed in a breaking way from ${oldType}.`;
    }
    return `${method} ${path} response changed in a breaking way.`;
  }

  if (result.tag?.startsWith("COMPAT_ERR:ENDPOINT_BODY") && method && path) {
    return `${method} ${path} request body changed in a breaking way.`;
  }

  if (result.tag?.startsWith("COMPAT_ERR:ENDPOINT_PARAMETER") && method && path) {
    if (parameter) {
      return `${method} ${path} changed parameter ${parameter} in a breaking way.`;
    }
    return `${method} ${path} changed request parameters in a breaking way.`;
  }

  if (result.tag?.startsWith("COMPAT_ERR:COMPONENT") && component) {
    if (property) {
      return `Shared component ${component} changed property ${property} in a breaking way.`;
    }
    return `Shared component ${component} changed in a breaking way.`;
  }

  return describeTag(result.tag);
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

function priorityForKey(key: string): number {
  const priorities: Record<string, number> = {
    path: 0,
    method: 1,
    component: 2,
    property: 3,
    parameter: 4,
    old_type: 5,
    new_type: 6,
    response_status: 7,
    status: 8,
  };

  return priorities[key] ?? 99;
}

const ResultDisplay = ({ result }: ResultDisplayProps) => {
  const [logsOpen, setLogsOpen] = useState(false);
  const [copiedKey, setCopiedKey] = useState<string | null>(null);

  if (!result) return null;

  const isCompatible = result.tag === "COMPAT_OK";
  const category = classifyTag(result.tag);
  const allContextEntries = Object.entries(result.context ?? {});
  const contextEntries = [...allContextEntries].sort(([leftKey], [rightKey]) => priorityForKey(leftKey) - priorityForKey(rightKey));
  const diagnosis = buildDiagnosis(result, contextEntries);
  const keyFacts = contextEntries.filter(([key]) => ["path", "method", "component", "property", "parameter", "old_type", "new_type"].includes(key));
  const summaryText = [
    `Diagnosis: ${diagnosis}`,
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
      <div
        className={
          isCompatible
            ? "rounded-xl border border-success/20 bg-card p-5 shadow-sm"
            : category === "Internal Error"
            ? "rounded-xl border border-amber-300/40 bg-card p-5 shadow-sm"
            : category === "Input Error" || category === "Well-Formedness Error"
            ? "rounded-xl border border-amber-400/40 bg-card p-5 shadow-sm"
            : "rounded-xl border border-destructive/20 bg-card p-5 shadow-sm"
        }
      >
        <div className="flex flex-wrap items-start justify-between gap-3">
          {isCompatible ? (
            <div className="inline-flex items-center gap-2.5 rounded-md border border-success/30 bg-success/10 px-4 py-2.5">
              <CheckCircle2 className="h-5 w-5 text-success" />
              <span className="text-sm font-semibold text-success">Compatible</span>
            </div>
          ) : category === "Internal Error" ? (
            <div className="inline-flex items-center gap-2.5 rounded-md border border-amber-400/30 bg-amber-400/10 px-4 py-2.5">
              <Wrench className="h-5 w-5 text-amber-600" />
              <span className="text-sm font-semibold text-amber-700">Internal Error</span>
            </div>
          ) : category === "Input Error" || category === "Well-Formedness Error" ? (
            <div className="inline-flex items-center gap-2.5 rounded-md border border-amber-400/30 bg-amber-400/10 px-4 py-2.5">
              <AlertTriangle className="h-5 w-5 text-amber-600" />
              <span className="text-sm font-semibold text-amber-700">{category}</span>
            </div>
          ) : (
            <div className="inline-flex items-center gap-2.5 rounded-md border border-destructive/30 bg-destructive/10 px-4 py-2.5">
              <XCircle className="h-5 w-5 text-destructive" />
              <span className="text-sm font-semibold text-destructive">Incompatible</span>
            </div>
          )}

          <p className="text-[11px] text-muted-foreground">Completed in {result.duration_ms} ms</p>
        </div>

        <p className="mt-4 text-base font-semibold text-foreground">{diagnosis}</p>

        {keyFacts.length > 0 && (
          <div className="mt-4 flex flex-wrap gap-2">
            {keyFacts.map(([key, value]) => (
              <span
                key={`${key}:${value}`}
                className="rounded-full border border-border bg-muted/60 px-3 py-1 text-xs text-foreground"
              >
                <span className="font-medium">{labelContextKey(key)}:</span> <span className="font-mono">{value}</span>
              </span>
            ))}
          </div>
        )}

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

        {result.logs.length > 0 && (
          <div className="mt-5 border-t border-border pt-4">
            <button
              onClick={() => setLogsOpen(!logsOpen)}
              className="inline-flex items-center gap-1 text-xs font-medium text-muted-foreground transition-colors hover:text-foreground"
            >
              {logsOpen ? <ChevronDown className="h-3.5 w-3.5" /> : <ChevronRight className="h-3.5 w-3.5" />}
              Debug Output
            </button>
            {logsOpen && (
              <pre className="mt-3 max-h-56 overflow-auto rounded-md border border-border bg-muted/40 px-3 py-2 text-left font-mono text-[11px] text-muted-foreground">
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
