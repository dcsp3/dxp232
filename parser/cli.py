import sys

from loader import load_spec, basic_openapi_sanity_check, OpenAPILoadError


def main():
    if len(sys.argv) != 2:
        print("Usage: python cli.py <openapi.yaml>")
        sys.exit(1)

    path = sys.argv[1]

    try:
        spec = load_spec(path)
        print("✔ YAML loaded successfully.")

        basic_openapi_sanity_check(spec)
        print("✔ Basic OpenAPI structure looks valid.")

        print("Top-level keys:", list(spec.keys()))

    except OpenAPILoadError as e:
        print(f"✘ Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()