import Header from "@/components/Header";
import { ShieldCheck, Code, Server, Layers, ArrowRight } from "lucide-react";

const About = () => {
  return (
    <div className="flex min-h-screen flex-col bg-background selection:bg-primary/20">
      <Header />
      
      <main className="mx-auto w-full max-w-4xl flex-1 px-6 py-12 lg:py-16">
        <div className="space-y-12">
          
          <section className="space-y-4 text-center">
            <div className="mx-auto flex h-20 w-20 items-center justify-center rounded-2xl bg-primary/10 mb-6">
              <ShieldCheck className="h-10 w-10 text-primary" />
            </div>
            <h1 className="text-4xl font-extrabold tracking-tight lg:text-5xl">
              Formal Verification for <span className="text-primary bg-clip-text text-transparent bg-gradient-to-r from-primary to-blue-500">APIs</span>
            </h1>
            <p className="mx-auto max-w-2xl text-lg text-muted-foreground">
              A formally verified tool for checking backward compatibility between two OpenAPI specifications.
            </p>
          </section>

          <section className="space-y-8 rounded-3xl bg-secondary/30 p-8 lg:p-12">
            <div className="text-center">
              <h2 className="text-3xl font-bold tracking-tight">How it Works</h2>
              <p className="mt-2 text-muted-foreground">The end-to-end compatibility checking process.</p>
            </div>

            <div className="grid gap-8 md:grid-cols-3">
              <div className="flex flex-col items-center text-center">
                <div className="mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-background shadow-sm border">
                  <Code className="h-6 w-6 text-foreground/70" />
                </div>
                <h4 className="font-semibold">1. Parsing</h4>
                <p className="mt-2 text-sm text-muted-foreground">
                  Python ingests the OpenAPI specs and translates them into a typed intermediate representation.
                </p>
              </div>

              <div className="flex flex-col items-center text-center relative">
                <div className="hidden md:block absolute top-7 left-[-2rem] w-[4rem] text-muted-foreground/30">
                  <ArrowRight className="mx-auto" />
                </div>
                <div className="mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-background shadow-sm border">
                  <Layers className="h-6 w-6 text-primary" />
                </div>
                <h4 className="font-semibold">2. Verification</h4>
                <p className="mt-2 text-sm text-muted-foreground">
                  The Agda core formally checks the typed structures for compatibility and strict non-breaking guarantees.
                </p>
              </div>

              <div className="flex flex-col items-center text-center relative">
                <div className="hidden md:block absolute top-7 left-[-2rem] w-[4rem] text-muted-foreground/30">
                  <ArrowRight className="mx-auto" />
                </div>
                <div className="mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-background shadow-sm border">
                  <Server className="h-6 w-6 text-foreground/70" />
                </div>
                <h4 className="font-semibold">3. Evaluation</h4>
                <p className="mt-2 text-sm text-muted-foreground">
                  The FastAPI backend processes the results and the React frontend displays detailed compatibility insights.
                </p>
              </div>
            </div>
          </section>
        </div>
      </main>
    </div>
  );
};

export default About;
