import { Link, useLocation } from "react-router-dom";

const NAV_LINKS = [
  { to: "/examples", label: "Examples" },
  { to: "/about", label: "About" },
];

const Header = () => {
  const { pathname } = useLocation();

  return (
    <header className="border-b border-border bg-card/60 backdrop-blur-md">
      <div className="mx-auto flex max-w-5xl items-center justify-between px-6 py-4">
        <div>
          <Link to="/" className="group block">
            <h1 className="text-base font-semibold tracking-tight text-foreground">
              OpenAPI Compatibility Checker
            </h1>

          </Link>
        </div>

        <nav className="flex items-center gap-1.5">
          {pathname !== "/" && (
            <Link
              to="/"
              className="rounded-md border border-border bg-secondary px-3 py-1.5 text-xs font-medium text-secondary-foreground transition-colors hover:bg-accent hover:text-foreground"
            >
              ← Checker
            </Link>
          )}
          {NAV_LINKS.map(({ to, label }) => {
            const isActive = pathname === to;
            return (
              <Link
                key={to}
                to={to}
                className={`rounded-md border px-3 py-1.5 text-xs font-medium transition-colors ${
                  isActive
                    ? "border-primary bg-primary text-primary-foreground"
                    : "border-border bg-secondary text-secondary-foreground hover:bg-accent hover:text-foreground"
                }`}
              >
                {label}
              </Link>
            );
          })}
        </nav>
      </div>
    </header>
  );
};

export default Header;
