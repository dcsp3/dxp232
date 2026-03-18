import { CheckCircle2, XCircle, ChevronDown, ChevronRight, Copy, Check, AlertTriangle, Wrench } from "lucide-react";
import { useState } from "react";
import type { CheckResponse } from "@/lib/api";

interface ResultDisplayProps {
  result: CheckResponse | null;
}

function classifyTag(tag: string | null): string {
  if (!tag) return "Unknown";
  if (tag === "COMPAT_OK") return "Compatible";
  if (tag.startsWith("TRANSLATION_ERR")) return "Input Error";
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

    case "COMPAT_ERR:ENDPOINT_REMOVED":
      return "An endpoint present in the old API is missing in the new API.";
    case "COMPAT_ERR:ENDPOINT_ROUTE_CHANGED":
      return "An endpoint changed its route between versions.";
    case "COMPAT_ERR:ENDPOINT_METHOD_CHANGED":
      return "An endpoint changed its HTTP method between versions.";
    case "COMPAT_ERR:ENDPOINT_PARAMETER_REMOVED":
      return "A parameter present in the old API has been removed.";
    case "COMPAT_ERR:ENDPOINT_REQUIRED_PARAMETER_ADDED":
      return "An optional parameter has been made required.";
    case "COMPAT_ERR:ENDPOINT_NEW_REQUIRED_PARAMETER":
      return "A new required parameter was added to an endpoint.";
    case "COMPAT_ERR:ENDPOINT_PARAMETER_SCHEMA_CHANGED":
      return "A parameter's type changed between versions.";
    case "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PRIMITIVE_CHANGED":
      return "An endpoint's request body type changed.";
    case "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_SHAPE_MISMATCH":
      return "An endpoint's request body changed its structural shape.";
    case "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_REQUIRED_FIELD_REMOVED":
      return "A required field was removed from an endpoint's request body.";
    case "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PROPERTY_REMOVED":
      return "A property was removed from an endpoint's request body.";
    case "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PROPERTY_DRIFT":
      return "A request body property changed its type.";
    case "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_ARRAY_ITEM_DRIFT":
      return "A request body array's item type changed.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_REMOVED":
      return "A response status has been removed from an endpoint.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PRIMITIVE_CHANGED":
      return "An endpoint's response type changed.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_SHAPE_MISMATCH":
      return "An endpoint's response changed its structural shape.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_REQUIRED_FIELD_REMOVED":
      return "A required field was removed from an endpoint's response.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PROPERTY_REMOVED":
      return "A property was removed from an endpoint's response.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PROPERTY_DRIFT":
      return "A response property changed its type.";
    case "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_ARRAY_ITEM_DRIFT":
      return "A response array's item type changed.";
    case "COMPAT_ERR:COMPONENT_REMOVED":
      return "A shared component schema present in the old API has been removed.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_PRIMITIVE_CHANGED":
      return "A component schema's primitive type changed.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_SHAPE_MISMATCH":
      return "A component schema changed its structural shape.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_REQUIRED_FIELD_REMOVED":
      return "A required field was removed from a component schema.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_REMOVED":
      return "A property was removed from a component schema.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_DRIFT":
      return "A component property changed its type.";
    case "COMPAT_ERR:COMPONENT_SCHEMA_ARRAY_ITEM_DRIFT":
      return "A component schema's array item type changed.";

    case "TRANSLATION_ERR:PATH_PARAMETER_NOT_REQUIRED":
      return "A path parameter must be marked required: true.";
    case "TRANSLATION_ERR:PATH_LEVEL_PARAMETERS_UNSUPPORTED":
      return "Path-level parameters are not supported; declare them on each operation instead.";
    case "TRANSLATION_ERR:METHOD_UNSUPPORTED":
      return "The endpoint uses an HTTP method not supported by this checker.";
    case "TRANSLATION_ERR:PARAMETER_UNSUPPORTED_LOCATION":
      return "A parameter uses an unsupported location (only path and query are supported).";
    case "TRANSLATION_ERR:PARAMETER_NON_PRIMITIVE":
      return "A parameter must have a primitive schema type.";
    case "TRANSLATION_ERR:STATUS_UNSUPPORTED":
      return "A response uses a status code not supported by this checker.";
    case "TRANSLATION_ERR:REQUEST_BODY_MISSING":
      return "An endpoint is missing a required request body.";
    case "TRANSLATION_ERR:BODY_UNSUPPORTED_METHOD":
      return "An endpoint uses an unsupported method and request body combination.";

    case "WF_ERR:API_DUPLICATE_COMPONENTS":
      return "The specification has duplicate component definitions.";
    case "WF_ERR:API_DUPLICATE_ENDPOINTS":
      return "The specification has duplicate endpoint definitions.";
    case "WF_ERR:API_ENDPOINT_DUPLICATE_PARAMETERS":
      return "An endpoint has duplicate parameter names.";
    case "WF_ERR:API_ENDPOINT_DUPLICATE_STATUSES":
      return "An endpoint declares the same response status code more than once.";
    case "WF_ERR:API_ENDPOINT_PATH_ILL_FORMED":
      return "An endpoint has an ill-formed path.";

    default:
      if (tag.startsWith("TRANSLATION_ERR"))
        return "The YAML could not be translated into the supported OpenAPI subset.";
      if (tag.startsWith("WF_ERR"))
        return "The specification failed formal well-formedness checks.";
      if (tag.startsWith("COMPAT_ERR"))
        return "The APIs are not compatible under the formal refinement relation.";
      if (tag.startsWith("BACKEND_ERROR") || tag.startsWith("COMPAT_CHECK_ERROR"))
        return "The backend encountered an internal failure while running the check.";
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
  const diagnosis = describeTag(result.tag);
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
