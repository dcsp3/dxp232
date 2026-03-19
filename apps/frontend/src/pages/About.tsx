import Header from "@/components/Header";

const About = () => {
  return (
    <div className="flex min-h-screen flex-col bg-background">
      <Header />
      <main className="mx-auto w-full max-w-2xl flex-1 px-6 py-8">
        <h1 className="text-3xl font-bold">About</h1>
        <p className="mt-4 text-muted-foreground">More information coming soon.</p>
      </main>
    </div>
  );
};

export default About;
