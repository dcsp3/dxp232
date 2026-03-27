from dsl_ast import Schema, SchemaRef, Path, PathSegment, Body, Endpoint, Parameter, Response, API

STATUS_MAP = {
    "200": "OK",
    "400": "BadRequest",
    "404": "NotFound",
    "204": "NoContent",
}

ALLOWED_METHODS = {"get", "post", "put", "delete", "patch"}

class TranslationError(Exception):
    def __init__(self, code: str, detail: str, context: dict[str, str] | None = None):
        super().__init__(detail)
        self.code = code
        self.detail = detail
        self.context = context or {}


def _fail(code: str, detail: str, **context: str) -> None:
    raise TranslationError(code, detail, context)


def _items(d: dict):
    if hasattr(d, "items_all"):
        return d.items_all()
    return d.items()


def _ensure_only_allowed_schema_fields(raw: dict, allowed: set[str], schema_kind: str) -> None:
    for field_name in raw:
        if field_name not in allowed:
            _fail(
                "SCHEMA_UNKNOWN_FIELD",
                f"{schema_kind} schema uses unsupported field '{field_name}'.",
                schema_kind=schema_kind,
                field=field_name,
            )


def _ensure_no_unexpected_schema_fields(raw: dict, forbidden: dict[str, str], schema_kind: str) -> None:
    for field_name, reason in forbidden.items():
        if field_name in raw:
            _fail(
                "SCHEMA_UNEXPECTED_FIELD",
                f"{schema_kind} schema cannot define '{field_name}'{reason}.",
                schema_kind=schema_kind,
                field=field_name,
            )


def translate_schema(raw: dict, components: dict) -> Schema:
    if not isinstance(raw, dict):
        _fail("SCHEMA_NOT_OBJECT", "Schema must be an object.")

    # resolve $ref
    if "$ref" in raw:
        _ensure_only_allowed_schema_fields(raw, {"$ref"}, "Ref")
        ref_value = raw["$ref"]

        if not ref_value.startswith("#/components/schemas/"):
            _fail("REF_UNSUPPORTED_FORMAT", f"Unsupported $ref format: {ref_value}", ref=ref_value)

        schema_name = ref_value.split("/")[-1]

        if schema_name not in components:
            _fail(
                "REF_SCHEMA_NOT_FOUND",
                f"Referenced schema '{schema_name}' not found.",
                schema=schema_name,
            )

        return SchemaRef(schema_name)

    if "type" not in raw:
        _fail("SCHEMA_MISSING_TYPE", "Schema missing 'type'.")

    base_type = raw["type"]

    # primitive
    if base_type in {"integer", "string", "boolean", "number"}:
        _ensure_only_allowed_schema_fields(raw, {"type", "properties", "required", "items"}, f"Primitive '{base_type}'")
        properties = []
        raw_props = raw.get("properties", {})
        if not isinstance(raw_props, dict):
            _fail("OBJECT_PROPERTIES_NOT_OBJECT", "'properties' must be an object.")
        for prop_name, prop_schema in _items(raw_props):
            translated_prop = translate_schema(prop_schema, components)
            properties.append((prop_name, translated_prop))

        required = raw.get("required", [])
        if not isinstance(required, list):
            _fail("OBJECT_REQUIRED_NOT_LIST", "'required' must be a list.")

        translated_items = None
        if "items" in raw:
            translated_items = translate_schema(raw["items"], components)

        return Schema(
            type=base_type,
            properties=properties,
            required=required,
            items=translated_items,
        )

    # objects
    if base_type == "object":
        _ensure_only_allowed_schema_fields(raw, {"type", "properties", "required", "items"}, "Object")
        properties = []
        raw_props = raw.get("properties", {})

        if not isinstance(raw_props, dict):
            _fail("OBJECT_PROPERTIES_NOT_OBJECT", "'properties' must be an object.")

        for prop_name, prop_schema in raw_props.items():
            translated_prop = translate_schema(prop_schema, components)
            properties.append((prop_name, translated_prop))

        required = raw.get("required", [])
        if not isinstance(required, list):
            _fail("OBJECT_REQUIRED_NOT_LIST", "'required' must be a list.")

        translated_items = None
        if "items" in raw:
            translated_items = translate_schema(raw["items"], components)

        return Schema(
            type="object",
            properties=properties,
            required=required,
            items=translated_items,
        )

    # arrays
    if base_type == "array":
        _ensure_only_allowed_schema_fields(raw, {"type", "items", "properties", "required"}, "Array")
        translated_items = None
        if "items" in raw:
            translated_items = translate_schema(raw["items"], components)

        properties = []
        raw_props = raw.get("properties", {})
        if not isinstance(raw_props, dict):
            _fail("OBJECT_PROPERTIES_NOT_OBJECT", "'properties' must be an object.")
        for prop_name, prop_schema in _items(raw_props):
            translated_prop = translate_schema(prop_schema, components)
            properties.append((prop_name, translated_prop))

        required = raw.get("required", [])
        if not isinstance(required, list):
            _fail("OBJECT_REQUIRED_NOT_LIST", "'required' must be a list.")

        return Schema(
            type="array",
            properties=properties,
            required=required,
            items=translated_items,
        )

    _fail("SCHEMA_UNSUPPORTED_TYPE", f"Base type '{base_type}' not supported yet", type=base_type)


def translate_path(path_str: str) -> Path:
    if not path_str.startswith("/"):
        _fail("PATH_INVALID_FORMAT", f"Invalid path format: {path_str}", path=path_str)

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
        _fail("REQUEST_BODY_MISSING", f"{method} operation missing requestBody.", method=method)

    request_body = operation["requestBody"]

    content = request_body.get("content", {})
    json_content = content.get("application/json")

    if json_content is None:
        _fail(
            "REQUEST_BODY_MISSING_JSON_CONTENT",
            f"{method} requestBody missing application/json content.",
            method=method,
        )

    if "schema" not in json_content:
        _fail("REQUEST_BODY_MISSING_SCHEMA", f"{method} requestBody missing schema.", method=method)

    raw_schema = json_content["schema"]
    translated_schema = translate_schema(raw_schema, components)

    if method == "POST":
        return Body(kind="HasBody", schema=translated_schema)
    if method == "PUT":
        return Body(kind="HasBodyU", schema=translated_schema)
    if method == "PATCH":
        return Body(kind="HasBodyP", schema=translated_schema)

    _fail("BODY_UNSUPPORTED_METHOD", f"Unsupported method for body: {method}", method=method)

def translate_method(method_str: str) -> str:
    if method_str.lower() not in ALLOWED_METHODS:
        _fail("METHOD_UNSUPPORTED", f"Unsupported HTTP method: {method_str}", method=method_str)

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

    _fail("BODY_UNSUPPORTED_METHOD", f"Unsupported method for body: {method}", method=method)

def translate_parameter(raw_param: dict) -> Parameter:
    name = raw_param.get("name")
    location = raw_param.get("in")
    required = raw_param.get("required", False)

    if location not in {"path", "query"}:
        _fail("PARAMETER_UNSUPPORTED_LOCATION", f"Unsupported parameter location: {location}", parameter=name or "", location=str(location))

    if "schema" not in raw_param:
        _fail("PARAMETER_MISSING_SCHEMA", f"Parameter '{name}' missing schema.", parameter=name or "")

    schema_obj = raw_param["schema"]

    if "type" not in schema_obj:
        _fail("PARAMETER_SCHEMA_MISSING_TYPE", f"Parameter '{name}' schema missing type.", parameter=name or "")

    base_type = schema_obj["type"]

    if base_type not in {"integer", "string", "boolean", "number"}:
        _fail("PARAMETER_NON_PRIMITIVE", f"Parameter '{name}' must have primitive type.", parameter=name or "", type=str(base_type))

    # let agda handle this

    # path params must be required
    # if location == "path" and not required:
    #     _fail("PATH_PARAMETER_NOT_REQUIRED", f"Path parameter '{name}' must be required.", parameter=name or "")

    return Parameter(
        name=name,
        location=location,
        required=required,
        schema=base_type,
    )

def translate_responses(raw_responses: dict, components: dict) -> list[Response]:
    translated = []

    for status_code, response_obj in _items(raw_responses):

        if status_code not in STATUS_MAP:
            _fail("STATUS_UNSUPPORTED", f"Unsupported status code: {status_code}", status=status_code)

        dsl_status = STATUS_MAP[status_code]

        content = response_obj.get("content", {})
        json_content = content.get("application/json")

        if json_content is None:
            _fail(
                "RESPONSE_MISSING_JSON_CONTENT",
                f"Response {status_code} missing application/json content.",
                status=status_code,
            )

        if "schema" not in json_content:
            _fail("RESPONSE_MISSING_SCHEMA", f"Response {status_code} missing schema.", status=status_code)

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

    translated_components = [
        (name, translate_schema(raw_schema, components_dict))
        for name, raw_schema in _items(components_dict)
    ]

    translated_paths = []
    raw_paths = spec.get("paths", {})

    for path_str, path_item in _items(raw_paths):

        translated_path = translate_path(path_str)
        path_level_params = path_item.get("parameters", []) if isinstance(path_item, dict) else []
        if path_level_params:
            _fail(
                "PATH_LEVEL_PARAMETERS_UNSUPPORTED",
                "Path-level parameters are not supported.",
                path=path_str,
            )

        for method_str, operation in _items(path_item):
            if method_str.lower() not in ALLOWED_METHODS:
                continue

            method = translate_method(method_str)

            raw_parameters = path_level_params + operation.get("parameters", [])
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
