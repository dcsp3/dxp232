from dsl_ast import Schema, Path, PathSegment, Body, Endpoint, Parameter, Response, API

ALLOWED_BASE_TYPES = {
    "integer",
    "string",
    "boolean",
    "number",
    "object",
    "array",
}

STATUS_MAP = {
    "200": "OK",
    "400": "BadRequest",
    "404": "NotFound",
    "204": "NoContent",
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

def translate_request_body(method: str, operation: dict, components: dict) -> Body:
    if method in {"GET", "DELETE"}:
        return default_body_for_method(method)

    if "requestBody" not in operation:
        raise TranslationError(f"{method} operation missing requestBody.")

    request_body = operation["requestBody"]

    content = request_body.get("content", {})
    json_content = content.get("application/json")

    if json_content is None:
        raise TranslationError(
            f"{method} requestBody missing application/json content."
        )

    if "schema" not in json_content:
        raise TranslationError(
            f"{method} requestBody missing schema."
        )

    raw_schema = json_content["schema"]
    translated_schema = translate_schema(raw_schema, components)

    if method == "POST":
        return Body(kind="HasBody", schema=translated_schema)
    if method == "PUT":
        return Body(kind="HasBodyU", schema=translated_schema)
    if method == "PATCH":
        return Body(kind="HasBodyP", schema=translated_schema)

    raise TranslationError(f"Unsupported method for body: {method}")

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

def translate_parameter(raw_param: dict) -> Parameter:
    name = raw_param.get("name")
    location = raw_param.get("in")
    required = raw_param.get("required", False)

    if location not in {"path", "query"}:
        raise TranslationError(f"Unsupported parameter location: {location}")

    if "schema" not in raw_param:
        raise TranslationError(f"Parameter '{name}' missing schema.")

    schema_obj = raw_param["schema"]

    if "type" not in schema_obj:
        raise TranslationError(f"Parameter '{name}' schema missing type.")

    base_type = schema_obj["type"]

    if base_type not in {"integer", "string", "boolean", "number"}:
        raise TranslationError(
            f"Parameter '{name}' must have primitive type."
        )

    # path params must be required
    if location == "path" and not required:
        raise TranslationError(
            f"Path parameter '{name}' must be required."
        )

    return Parameter(
        name=name,
        location=location,
        required=required,
        schema=base_type,
    )

def translate_responses(raw_responses: dict, components: dict) -> list[Response]:
    translated = []

    for status_code, response_obj in raw_responses.items():

        if status_code not in STATUS_MAP:
            raise TranslationError(
                f"Unsupported status code: {status_code}"
            )

        dsl_status = STATUS_MAP[status_code]

        content = response_obj.get("content", {})
        json_content = content.get("application/json")

        if json_content is None:
            raise TranslationError(
                f"Response {status_code} missing application/json content."
            )

        if "schema" not in json_content:
            raise TranslationError(
                f"Response {status_code} missing schema."
            )

        raw_schema = json_content["schema"]

        translated_schema = translate_schema(raw_schema, components)

        translated.append(
            Response(
                status=dsl_status,
                schema=translated_schema,
            )
        )

    return translated

def translate_api(spec: dict) -> API:
    components_dict = spec.get("components", {}).get("schemas", {})

    translated_components = []
    for name, raw_schema in components_dict.items():
        translated_schema = translate_schema(raw_schema, components_dict)
        translated_components.append((name, translated_schema))

    translated_paths = []
    raw_paths = spec.get("paths", {})

    for path_str, path_item in raw_paths.items():
        translated_path = translate_path(path_str)

        for method_str, operation in path_item.items():
            method = translate_method(method_str)

            raw_parameters = operation.get("parameters", [])
            translated_parameters = [
                translate_parameter(p) for p in raw_parameters
            ]

            raw_responses = operation.get("responses", {})
            translated_responses = translate_responses(raw_responses, components_dict)

            endpoint = Endpoint(
                route=translated_path,
                method=method,
                parameters=translated_parameters,
                body=translate_request_body(method, operation, components_dict),
                responses=translated_responses,
            )

            translated_paths.append(endpoint)

    return API(
        paths=translated_paths,
        components=translated_components,
    )
