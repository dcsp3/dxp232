import { useState } from "react";
import { useNavigate } from "react-router-dom";
import {
  CheckCircle2,
  XCircle,
  AlertTriangle,
  ArrowRight,
  BookOpen,
} from "lucide-react";
import Header from "@/components/Header";
import { EXAMPLES, type ExampleCategory, type ExamplePair } from "@/data/examples";


type FilterValue = "all" | ExampleCategory;

const FILTERS: { value: FilterValue; label: string }[] = [
  { value: "all", label: "All" },
  { value: "compatible", label: "Compatible" },
  { value: "breaking", label: "Breaking Changes" },
  { value: "input-error", label: "Input Errors" },
];

function categoryMeta(category: ExampleCategory) {
  switch (category) {
    case "compatible":
      return {
        icon: <CheckCircle2 className="h-3.5 w-3.5" />,
        cardBorder: "border-success/20",
        tagClass: "bg-success/10 text-success",
      };
    case "breaking":
      return {
        icon: <XCircle className="h-3.5 w-3.5" />,
        cardBorder: "border-destructive/20",
        tagClass: "bg-destructive/10 text-destructive",
      };
    case "input-error":
      return {
        icon: <AlertTriangle className="h-3.5 w-3.5" />,
        cardBorder: "border-amber-400/20",
        tagClass: "bg-amber-400/10 text-amber-700",
      };
  }
}


function ExampleCard({ example }: { example: ExamplePair }) {
  const navigate = useNavigate();
  const meta = categoryMeta(example.category);

  function handleLoad() {
    navigate("/", {
      state: { oldSpec: example.old, newSpec: example.new, fromExample: example.id },
    });
  }

  return (
    <div className={`flex flex-col rounded-xl border ${meta.cardBorder} bg-card shadow-sm transition-shadow hover:shadow-md`}>
      <div className="p-5 pb-3">
        <div className="flex items-center gap-2 mb-1.5">
          <span className={meta.tagClass}>{meta.icon}</span>
          <h3 className="text-sm font-semibold text-foreground leading-snug">
            {example.title}
          </h3>
        </div>
        <p className="text-xs text-muted-foreground leading-relaxed">
          {example.description}
        </p>
      </div>

      <div className="px-5 py-2.5 border-t border-border flex flex-col gap-1.5">
        <p className="text-xs text-foreground/80">
          <span className="text-[10px] font-semibold uppercase tracking-wider text-muted-foreground mr-2">Change</span>
          {example.change}
        </p>
        <p className="text-xs">
          <span className="text-[10px] font-semibold uppercase tracking-wider text-muted-foreground mr-2">Result</span>
          <span className={`inline-block rounded px-1.5 py-0.5 font-mono text-[11px] ${meta.tagClass}`}>
            {example.expectedTag}
          </span>
        </p>
      </div>

      <div className="border-t border-border px-5 py-3 flex items-center gap-2">
        <button
          onClick={handleLoad}
          className="ml-auto inline-flex items-center gap-1.5 rounded-md bg-primary px-3 py-1.5 text-xs font-semibold text-primary-foreground shadow-sm shadow-primary/20 transition-all hover:brightness-110"
        >
          Load in Checker
          <ArrowRight className="h-3.5 w-3.5" />
        </button>
      </div>
    </div>
  );
}


const Examples = () => {
  const [activeFilter, setActiveFilter] = useState<FilterValue>("all");

  const filtered =
    activeFilter === "all"
      ? EXAMPLES
      : EXAMPLES.filter((e) => e.category === activeFilter);

  return (
    <div className="flex min-h-screen flex-col bg-background">
      <Header />

      <main className="mx-auto w-full max-w-5xl flex-1 px-6 py-8">
        <div className="flex items-start gap-3 mb-6">
          <div className="mt-0.5 flex h-9 w-9 shrink-0 items-center justify-center rounded-lg border border-border bg-card">
            <BookOpen className="h-4 w-4 text-muted-foreground" />
          </div>
          <div>
            <h1 className="text-xl font-bold tracking-tight text-foreground">Examples</h1>
            <p className="mt-1 text-sm text-muted-foreground">
              Example API changes covering compatible evolutions, breaking changes, and input errors, with the result the formal model produces for each.
              Click <span className="font-medium text-foreground">Load in Checker</span> to run any of them through the tool.
            </p>
          </div>
        </div>

        <div className="mb-6 flex flex-wrap gap-1.5">
          {FILTERS.map((f) => {
            const isActive = activeFilter === f.value;
            const count =
              f.value === "all"
                ? EXAMPLES.length
                : EXAMPLES.filter((e) => e.category === f.value).length;
            return (
              <button
                key={f.value}
                onClick={() => setActiveFilter(f.value)}
                className={`rounded-full border px-3.5 py-1.5 text-xs font-medium transition-colors ${
                  isActive
                    ? "border-primary bg-primary text-primary-foreground"
                    : "border-border bg-card text-muted-foreground hover:bg-muted hover:text-foreground"
                }`}
              >
                {f.label}
                <span
                  className={`ml-1.5 rounded-full px-1.5 py-0.5 text-[10px] font-semibold ${
                    isActive
                      ? "bg-primary-foreground/20 text-primary-foreground"
                      : "bg-muted text-muted-foreground"
                  }`}
                >
                  {count}
                </span>
              </button>
            );
          })}
        </div>

        <div className="grid grid-cols-1 gap-4 lg:grid-cols-2">
          {filtered.map((example) => (
            <ExampleCard key={example.id} example={example} />
          ))}
        </div>

        {filtered.length === 0 && (
          <div className="py-16 text-center text-sm text-muted-foreground">
            No examples in this category.
          </div>
        )}
      </main>

      <footer className="border-t border-border py-4 text-center text-[11px] text-muted-foreground">
        Compatibility results derived from a formal Agda model
      </footer>
    </div>
  );
};

export default Examples;

