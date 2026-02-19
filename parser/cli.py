import sys

from loader import load_spec, basic_openapi_sanity_check, OpenAPILoadError
from translate import translate_api, TranslationError
from printer import print_api_module

def main():
    if len(sys.argv) != 2:
        print("Usage: python cli.py <openapi.yaml>")
        sys.exit(1)

    path = sys.argv[1]

    try:
        spec = load_spec(path)
        basic_openapi_sanity_check(spec)

        api = translate_api(spec)

        module_code = print_api_module(api, "Generated.GeneratedAPI")

        with open("agda/Generated/GeneratedAPI.agda", "w", encoding="utf-8") as f:
            f.write(module_code)

        print("Generated agda/Generated/GeneratedAPI.agda")

    except (OpenAPILoadError, TranslationError) as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
