from dsl_ast import Schema, Path, PathSegment, Body, Endpoint, API

ALLOWED_BASE_TYPES = {
    "integer",
    "string",
    "boolean",
    "number",
    "object",
    "array",
}

ALLOWED_METHODS = {"get", "post", "put", "delete", "patch"}

class TranslationError(Exception):
    pass


def translate_schema(raw: dict, components: dict) -> Schema:
    if not isinstance(raw, dict):
        raise TranslationError("Schema must be an object.")
    
    # resolve $ref
    if "$ref" in raw:
        ref_value = raw["$ref"]

        if not ref_value.startswith("#/components/schemas/"):
            raise TranslationError(f"Unsupported $ref format: {ref_value}")

        schema_name = ref_value.split("/")[-1]

        if schema_name not in components:
            raise TranslationError(f"Referenced schema '{schema_name}' not found.")

        referenced_schema = components[schema_name]

        # recursively translate the referenced schema
        return translate_schema(referenced_schema, components)


    if "type" not in raw:
        raise TranslationError("Schema missing 'type' field.")

    base_type = raw["type"]

    if base_type not in ALLOWED_BASE_TYPES:
        raise TranslationError(f"Unsupported base type: {base_type}")

    # primitive only for now
    if base_type in {"integer", "string", "boolean", "number"}:
        return Schema(
            type=base_type,
            properties=[],
            required=[],
            items=None,
            enum=None,
            default=None,
            description=None,
            examples=[],
        )

    # objects
    if base_type == "object":
        properties = []
        raw_props = raw.get("properties", {})

        if not isinstance(raw_props, dict):
            raise TranslationError("'properties' must be an object.")

        for prop_name, prop_schema in raw_props.items():
            translated_prop = translate_schema(prop_schema, components)
            properties.append((prop_name, translated_prop))

        required = raw.get("required", [])
        if not isinstance(required, list):
            raise TranslationError("'required' must be a list.")

        return Schema(
            type="object",
            properties=properties,
            required=required,
            items=None,
            enum=None,
            default=None,
            description=None,
            examples=[],
        )
    
    # arrays
    if base_type == "array":
        if "items" not in raw:
            raise TranslationError("Array schema missing 'items'.")

        translated_items = translate_schema(raw["items"], components)

        return Schema(
            type="array",
            properties=[],
            required=[],
            items=translated_items,
            enum=None,
            default=None,
            description=None,
            examples=[],
        )

    raise TranslationError(
        f"Base type '{base_type}' not supported yet"
    )

def translate_path(path_str: str) -> Path:
    if not path_str.startswith("/"):
        raise TranslationError(f"Invalid path format: {path_str}")

    segments = []

    parts = path_str.strip("/").split("/")

    for part in parts:
        if part.startswith("{") and part.endswith("}"):
            param_name = part[1:-1]
            segments.append(PathSegment(kind="param", value=param_name))
        else:
            segments.append(PathSegment(kind="lit", value=part))

    return Path(segments=segments)

def translate_method(method_str: str) -> str:
    if method_str.lower() not in ALLOWED_METHODS:
        raise TranslationError(f"Unsupported HTTP method: {method_str}")

    return method_str.upper()

def default_body_for_method(method: str) -> Body:
    if method == "GET":
        return Body(kind="NoBody", schema=None)
    if method == "DELETE":
        return Body(kind="NoBodyD", schema=None)
    if method == "POST":
        return Body(kind="HasBody", schema=None)
    if method == "PUT":
        return Body(kind="HasBodyU", schema=None)
    if method == "PATCH":
        return Body(kind="HasBodyP", schema=None)

    raise TranslationError(f"Unsupported method for body: {method}")

def translate_api(spec: dict) -> API:
    components_dict = spec.get("components", {}).get("schemas", {})

    translated_components = []

    for name, raw_schema in components_dict.items():
        translated_schema = translate_schema(raw_schema, components_dict)
        translated_components.append((name, translated_schema))

        translated_paths = []

    raw_paths = spec.get("paths", {})

    for path_str in raw_paths.keys():
        translated_path = translate_path(path_str)

    translated_paths = []

    raw_paths = spec.get("paths", {})

    for path_str, path_item in raw_paths.items():
        translated_path = translate_path(path_str)

        for method_str, operation in path_item.items():
            method = translate_method(method_str)

            endpoint = Endpoint(
                route=translated_path,
                method=method,
                parameters=[],
                body=default_body_for_method(method),
                responses=[],
            )

            translated_paths.append(endpoint)

    return API(
        paths=translated_paths,
        components=translated_components,
    )