import { Check, Loader2 } from "lucide-react";

interface ProgressStepsProps {
  currentStep: number; // -1 = not started
  steps: string[];
  completed: boolean;
}

const ProgressSteps = ({ currentStep, steps, completed }: ProgressStepsProps) => {
  if (currentStep < 0) return null;

  return (
    <div className="mx-auto mt-4 flex max-w-xs flex-col gap-1.5">
      {steps.map((step, i) => {
        const stepCompleted = completed ? i <= currentStep : i < currentStep;
        const active = i === currentStep;

        return (
          <div key={step} className="flex items-center gap-2 text-xs">
            {stepCompleted ? (
              <Check className="h-3.5 w-3.5 text-success" />
            ) : active ? (
              <Loader2 className="h-3.5 w-3.5 animate-spin text-primary" />
            ) : (
              <div className="h-3.5 w-3.5 rounded-full border border-border" />
            )}
            <span
              className={
                stepCompleted
                  ? "text-success font-medium"
                  : active
                  ? "text-foreground font-medium"
                  : "text-muted-foreground"
              }
            >
              {step}
            </span>
          </div>
        );
      })}
    </div>
  );
};

export default ProgressSteps;
