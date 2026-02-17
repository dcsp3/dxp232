import sys

from loader import load_spec, basic_openapi_sanity_check, OpenAPILoadError
from translate import translate_schema, TranslationError


def main():
    if len(sys.argv) != 2:
        print("Usage: python cli.py <openapi.yaml>")
        sys.exit(1)

    path = sys.argv[1]

    try:
        spec = load_spec(path)
        print("YAML loaded successfully.")

        basic_openapi_sanity_check(spec)
        print("Basic OpenAPI structure looks valid.")

        print("Top-level keys:", list(spec.keys()))

        # translate component schemas
        if "components" in spec and "schemas" in spec["components"]:
            for name, schema in spec["components"]["schemas"].items():
                print(f"\nTranslating component: {name}")
                components = spec.get("components", {}).get("schemas", {})
                translated = translate_schema(schema, components)
                print("  -> OK:", translated)

        print("\nTranslation stage completed.")

    except (OpenAPILoadError, TranslationError) as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
