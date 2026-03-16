import { Link, useLocation } from "react-router-dom";

const Header = () => {
  const location = useLocation();
  const isAbout = location.pathname === "/about";

  return (
    <header className="border-b border-border bg-card/60 backdrop-blur-md">
      <div className="mx-auto flex max-w-5xl items-center justify-between px-6 py-4">
        <div>
          <Link to="/" className="group block">
            <h1 className="text-base font-semibold tracking-tight text-foreground">
              API Refinement Checker
            </h1>
            <p className="mt-0.5 text-xs text-muted-foreground">
              Formally Verified Compatibility for OpenAPI Specifications
            </p>
          </Link>
        </div>
        <Link
          to={isAbout ? "/" : "/about"}
          className="rounded-md border border-border bg-secondary px-3 py-1.5 text-xs font-medium text-secondary-foreground transition-colors hover:bg-accent hover:text-foreground"
        >
          {isAbout ? "← Back" : "About"}
        </Link>
      </div>
    </header>
  );
};

export default Header;
