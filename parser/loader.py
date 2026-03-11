import yaml


class OpenAPILoadError(Exception):
    pass


def load_spec(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
    except FileNotFoundError:
        raise OpenAPILoadError(f"File not found: {path}")
    except yaml.YAMLError as e:
        raise OpenAPILoadError(f"YAML parsing error: {e}")

    if not isinstance(data, dict):
        raise OpenAPILoadError("OpenAPI file must contain a top-level object.")

    return data


def basic_openapi_sanity_check(spec: dict) -> None:
    required_keys = ["openapi", "paths"]

    for key in required_keys:
        if key not in spec:
            raise OpenAPILoadError(f"Missing required OpenAPI field: '{key}'")

    if not isinstance(spec["paths"], dict):
        raise OpenAPILoadError("'paths' must be an object.")
