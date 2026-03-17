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
    case "COMPAT_ERR:COMPONENT_SCHEMA_SHAPE_MISMATCH":
      return "A shared component schema changed structural shape between versions.";
    case "COMPAT_ERR:ENDPOINT_REMOVED":
      return "An endpoint present in the old API is missing in the new API.";
    default:
      if (tag.startsWith("TRANSLATION_ERR")) {
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
  const status = context.response_status ?? context.status;

  const ep = method && path ? `${method} ${path}` : null;

  if (result.tag === "COMPAT_OK") {
    return "The candidate API preserves the existing contract for the cases checked.";
  }

  if (result.tag === "TRANSLATION_ERR:REQUEST_BODY_MISSING") {
    return ep ? `${ep} is missing a request body.` : method ? `${method} operation is missing a request body.` : "An operation is missing a request body.";
  }
  if (result.tag === "TRANSLATION_ERR:BODY_UNSUPPORTED_METHOD") {
    return ep ? `${ep} uses a method/body combination that is not supported.` : "An operation uses an unsupported method/body combination.";
  }
  if (result.tag === "TRANSLATION_ERR:METHOD_UNSUPPORTED") {
    return method ? `HTTP method ${method} is not supported by this checker.` : "An endpoint uses an unsupported HTTP method.";
  }
  if (result.tag === "TRANSLATION_ERR:PARAMETER_UNSUPPORTED_LOCATION") {
    return parameter ? `Parameter ${parameter} uses an unsupported location (only path and query are supported).` : "A parameter uses an unsupported location.";
  }
  if (result.tag === "TRANSLATION_ERR:PARAMETER_NON_PRIMITIVE") {
    return parameter ? `Parameter ${parameter} must have a primitive type.` : "A parameter must have a primitive type.";
  }
  if (result.tag === "TRANSLATION_ERR:PATH_PARAMETER_NOT_REQUIRED") {
    return parameter ? `Path parameter ${parameter} must be marked required.` : "A path parameter must be marked required.";
  }
  if (result.tag === "TRANSLATION_ERR:STATUS_UNSUPPORTED") {
    return status ? `Response status ${status} is not supported by this checker.` : "A response uses an unsupported status code.";
  }
  if (result.tag?.startsWith("TRANSLATION_ERR")) {
    return "The spec uses a feature outside the supported OpenAPI subset.";
  }

  if (result.tag === "WF_ERR:API_DUPLICATE_COMPONENTS") {
    return component ? `Duplicate component name: ${component}.` : "The spec has duplicate component names.";
  }
  if (result.tag === "WF_ERR:API_DUPLICATE_ENDPOINTS") {
    return ep ? `${ep} is defined more than once.` : "The spec has duplicate endpoint definitions.";
  }
  if (result.tag === "WF_ERR:API_ENDPOINT_DUPLICATE_PARAMETERS") {
    return ep && parameter ? `${ep} has duplicate parameter ${parameter}.` : ep ? `${ep} has duplicate parameters.` : "An endpoint has duplicate parameters.";
  }
  if (result.tag === "WF_ERR:API_ENDPOINT_DUPLICATE_STATUSES") {
    return ep && status ? `${ep} has duplicate ${status} response.` : ep ? `${ep} has duplicate response statuses.` : "An endpoint has duplicate response statuses.";
  }
  if (result.tag === "WF_ERR:API_ENDPOINT_PATH_ILL_FORMED") {
    return ep ? `${ep} has a path/parameter alignment problem.` : "An endpoint has an ill-formed path.";
  }
  if (result.tag?.startsWith("WF_ERR")) {
    return "The spec failed formal well-formedness checks.";
  }

  if (result.tag === "COMPAT_ERR:ENDPOINT_REMOVED") {
    return ep ? `${ep} no longer exists in the new API.` : "An endpoint was removed.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_ROUTE_CHANGED") {
    return ep ? `${ep} changed its route.` : "An endpoint changed its route.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_METHOD_CHANGED") {
    return ep ? `${ep} changed its HTTP method.` : "An endpoint changed its HTTP method.";
  }

  if (result.tag === "COMPAT_ERR:ENDPOINT_PARAMETER_REMOVED") {
    if (ep && parameter) return `${ep} removed parameter ${parameter}.`;
    if (ep) return `${ep} removed a parameter.`;
    return "An endpoint removed a parameter.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_REQUIRED_PARAMETER_ADDED") {
    if (ep && parameter) return `${ep} made parameter ${parameter} required.`;
    if (ep) return `${ep} made an optional parameter required.`;
    return "An endpoint made an optional parameter required.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_NEW_REQUIRED_PARAMETER") {
    if (ep && parameter) return `${ep} added a new required parameter ${parameter}.`;
    if (ep) return `${ep} added a new required parameter.`;
    return "An endpoint added a new required parameter.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_PARAMETER_SCHEMA_CHANGED") {
    if (ep && parameter && oldType && newType) return `${ep} changed parameter ${parameter} from ${oldType} to ${newType}.`;
    if (ep && parameter) return `${ep} changed the type of parameter ${parameter}.`;
    if (ep) return `${ep} changed a parameter's type.`;
    return "An endpoint changed a parameter's type.";
  }

  if (result.tag === "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PRIMITIVE_CHANGED") {
    if (ep && oldType && newType) return `${ep} changed its request body type from ${oldType} to ${newType}.`;
    if (ep) return `${ep} changed its request body type.`;
    return "An endpoint changed its request body type.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_SHAPE_MISMATCH") {
    return ep ? `${ep} changed its request body structure entirely.` : "An endpoint changed its request body structure.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_REQUIRED_FIELD_REMOVED") {
    if (ep && property) return `${ep} dropped required field ${property} from its request body.`;
    if (ep) return `${ep} dropped a required field from its request body.`;
    return "An endpoint dropped a required field from its request body.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PROPERTY_REMOVED") {
    if (ep && property) return `${ep} removed property ${property} from its request body.`;
    if (ep) return `${ep} removed a property from its request body.`;
    return "An endpoint removed a property from its request body.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PROPERTY_DRIFT") {
    if (ep && property) return `${ep} changed property ${property} in its request body.`;
    if (ep) return `${ep} changed a property in its request body.`;
    return "An endpoint changed a request body property.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_ARRAY_ITEM_DRIFT") {
    return ep ? `${ep} changed the item type of its request body array.` : "An endpoint changed its request body array item type.";
  }

  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_REMOVED") {
    if (ep && status) return `${ep} dropped the ${status} response.`;
    if (ep) return `${ep} dropped a response status.`;
    return "An endpoint dropped a response status.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PRIMITIVE_CHANGED") {
    if (ep && status && oldType && newType) return `${ep} ${status} response changed type from ${oldType} to ${newType}.`;
    if (ep && status) return `${ep} ${status} response changed its type.`;
    if (ep) return `${ep} changed a response type.`;
    return "An endpoint changed a response type.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_SHAPE_MISMATCH") {
    if (ep && status) return `${ep} ${status} response changed its structure entirely.`;
    return ep ? `${ep} changed a response's structure.` : "An endpoint changed a response structure.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_REQUIRED_FIELD_REMOVED") {
    if (ep && status && property) return `${ep} ${status} response dropped required field ${property}.`;
    if (ep && status) return `${ep} ${status} response dropped a required field.`;
    if (ep) return `${ep} dropped a required field from a response.`;
    return "An endpoint dropped a required field from a response.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PROPERTY_REMOVED") {
    if (ep && status && property) return `${ep} ${status} response removed property ${property}.`;
    if (ep && status) return `${ep} ${status} response removed a property.`;
    if (ep) return `${ep} removed a property from a response.`;
    return "An endpoint removed a property from a response.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PROPERTY_DRIFT") {
    if (ep && status && property) return `${ep} ${status} response changed property ${property}.`;
    if (ep && status) return `${ep} ${status} response changed a property.`;
    if (ep) return `${ep} changed a response property.`;
    return "An endpoint changed a response property.";
  }
  if (result.tag === "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_ARRAY_ITEM_DRIFT") {
    if (ep && status) return `${ep} ${status} response changed its array item type.`;
    return ep ? `${ep} changed a response array item type.` : "An endpoint changed a response array item type.";
  }

  if (result.tag === "COMPAT_ERR:COMPONENT_REMOVED") {
    return component ? `Component ${component} was removed.` : "A shared component was removed.";
  }
  if (result.tag === "COMPAT_ERR:COMPONENT_SCHEMA_PRIMITIVE_CHANGED") {
    if (component && oldType && newType) return `Component ${component} changed its type from ${oldType} to ${newType}.`;
    return component ? `Component ${component} changed its primitive type.` : "A component changed its primitive type.";
  }
  if (result.tag === "COMPAT_ERR:COMPONENT_SCHEMA_SHAPE_MISMATCH") {
    return component ? `Component ${component} changed its structural shape.` : "A component changed its structural shape.";
  }
  if (result.tag === "COMPAT_ERR:COMPONENT_SCHEMA_REQUIRED_FIELD_REMOVED") {
    if (component && property) return `Component ${component} dropped required field ${property}.`;
    return component ? `Component ${component} dropped a required field.` : "A component dropped a required field.";
  }
  if (result.tag === "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_REMOVED") {
    if (component && property) return `Component ${component} removed property ${property}.`;
    return component ? `Component ${component} removed a property.` : "A component removed a property.";
  }
  if (result.tag === "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_DRIFT") {
    if (component && property) return `Component ${component} changed property ${property}.`;
    return component ? `Component ${component} changed a property.` : "A component changed a property.";
  }
  if (result.tag === "COMPAT_ERR:COMPONENT_SCHEMA_ARRAY_ITEM_DRIFT") {
    return component ? `Component ${component} changed its array item type.` : "A component changed its array item type.";
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
