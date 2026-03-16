import type { KeyboardEvent } from "react";

interface YamlPanelProps {
  title: string;
  subtitle: string;
  value: string;
  onChange: (value: string) => void;
  onLoadExample: () => void;
}

const YamlPanel = ({ title, subtitle, value, onChange, onLoadExample }: YamlPanelProps) => {
  const indentUnit = "  ";

  const handleKeyDown = (event: KeyboardEvent<HTMLTextAreaElement>) => {
    if (event.key === "Tab") {
      event.preventDefault();
      const textarea = event.currentTarget;
      const start = textarea.selectionStart;
      const end = textarea.selectionEnd;
      const nextValue = `${value.slice(0, start)}${indentUnit}${value.slice(end)}`;

      onChange(nextValue);

      requestAnimationFrame(() => {
        textarea.selectionStart = start + indentUnit.length;
        textarea.selectionEnd = start + indentUnit.length;
      });
      return;
    }

    if (event.key !== "Enter" || event.shiftKey || event.ctrlKey || event.altKey || event.metaKey) {
      return;
    }

    event.preventDefault();

    const textarea = event.currentTarget;
    const start = textarea.selectionStart;
    const end = textarea.selectionEnd;
    const lineStart = value.lastIndexOf("\n", Math.max(0, start - 1)) + 1;
    const currentLine = value.slice(lineStart, start);
    const baseIndent = currentLine.match(/^\s*/)?.[0] ?? "";
    const extraIndent = currentLine.trimEnd().endsWith(":") ? indentUnit : "";
    const insertion = `\n${baseIndent}${extraIndent}`;
    const nextValue = `${value.slice(0, start)}${insertion}${value.slice(end)}`;

    onChange(nextValue);

    requestAnimationFrame(() => {
      const cursorPos = start + insertion.length;
      textarea.selectionStart = cursorPos;
      textarea.selectionEnd = cursorPos;
    });
  };

  return (
    <div className="flex flex-1 flex-col overflow-hidden rounded-lg border border-border bg-card">
      <div className="flex items-center justify-between border-b border-border px-4 py-3">
        <div className="flex items-center gap-2.5">
          <div className="h-2 w-2 rounded-full bg-primary/60" />
          <div>
            <h2 className="text-sm font-semibold text-foreground">{title}</h2>
            <p className="text-[11px] text-muted-foreground">{subtitle}</p>
          </div>
        </div>
        <button
          onClick={onLoadExample}
          className="rounded-md border border-border bg-secondary px-2.5 py-1 text-[11px] font-medium text-muted-foreground transition-colors hover:bg-accent hover:text-foreground"
        >
          Load Example
        </button>
      </div>
      <textarea
        value={value}
        onChange={(e) => onChange(e.target.value)}
        onKeyDown={handleKeyDown}
        placeholder="Paste OpenAPI YAML here…"
        spellCheck={false}
        className="flex-1 resize-none border-none bg-transparent px-4 py-3 font-mono text-[13px] leading-relaxed text-foreground placeholder:text-muted-foreground/40 focus:outline-none focus:ring-0"
        style={{ minHeight: "380px" }}
      />
    </div>
  );
};

export default YamlPanel;
