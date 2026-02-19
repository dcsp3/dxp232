from dsl_ast import  Schema, SchemaRef, Path, PathSegment, Endpoint, Response, Parameter, Body, API


def agda_list(items: list[str]) -> str:
    if not items:
        return "[]"

    result = items[-1]
    for item in reversed(items[:-1]):
        result = f"{item} :: {result}"

    return f"{result} :: []"

def print_schema(schema: Schema) -> str:
    if isinstance(schema, SchemaRef):
        return schema.name

    if schema.type in {"integer", "string", "boolean", "number"}:
        return (
            "record { "
            f"type = {schema.type} ; "
            "properties = [] ; "
            "required = [] ; "
            "items = nothing ; "
            "enum = nothing ; "
            "default = nothing ; "
            "description = nothing ; "
            "examples = [] }"
        )

    if schema.type == "object":
        props = []
        for name, sub in schema.properties:
            prop_str = f'("{name}" , {print_schema(sub)})'
            props.append(prop_str)

        properties_str = agda_list(props)
        required_str = agda_list([f'"{r}"' for r in schema.required])

        return (
            "record { "
            "type = object ; "
            f"properties = {properties_str} ; "
            f"required = {required_str} ; "
            "items = nothing ; "
            "enum = nothing ; "
            "default = nothing ; "
            "description = nothing ; "
            "examples = [] }"
        )

    if schema.type == "array":
        return (
            "record { "
            "type = array ; "
            "properties = [] ; "
            "required = [] ; "
            f"items = just ({print_schema(schema.items)}) ; "
            "enum = nothing ; "
            "default = nothing ; "
            "description = nothing ; "
            "examples = [] }"
        )

    raise ValueError(f"Unsupported schema type: {schema.type}")

def print_path_segment(seg: PathSegment) -> str:
    if seg.kind == "lit":
        return f'lit "{seg.value}"'
    if seg.kind == "param":
        return f'param "{seg.value}"'
    raise ValueError("Unknown PathSegment kind")

def print_path(path: Path) -> str:
    segments = [print_path_segment(s) for s in path.segments]
    segments_str = agda_list(segments)

    return f"record {{ segments = {segments_str} }}"

def print_parameter(p: Parameter) -> str:
    location = "path" if p.location == "path" else "query"

    required = "true" if p.required else "false"

    return (
        "record { "
        f"name = \"{p.name}\" ; "
        f"location = {location} ; "
        f"required = {required} ; "
        f"schema = {p.schema} }}"
    )

def print_body(body: Body):
    if body.kind in {"NoBody", "NoBodyD"}:
        return body.kind

    return f"{body.kind} {print_schema(body.schema)}"

def print_response(r: Response):
    return f"response {r.status} {print_schema(r.schema)}"

def print_endpoint(e: Endpoint) -> str:
    parameters_str = agda_list([print_parameter(p) for p in e.parameters])
    responses_str = agda_list([print_response(r) for r in e.responses])

    return (
        "record { "
        f"route = {print_path(e.route)} ; "
        f"method = {e.method} ; "
        f"parameters = {parameters_str} ; "
        f"body = {print_body(e.body)} ; "
        f"responses = {responses_str} }}"
    )

def print_api_module(api: API, module_name: str) -> str:
    lines = []

    component_map = {id(schema): name for name, schema in api.components}

    lines.append(f"module {module_name} where")
    lines.append("")
    lines.append("open import All")
    lines.append("")

    # Components
    for name, schema in api.components:
        lines.append(f"{name} : Schema")
        lines.append(f"{name} = {print_schema(schema)}")
        lines.append("")

    # Paths
    for i, endpoint in enumerate(api.paths):
        path_name = f"Path{i}"
        lines.append(f"{path_name} : Path")
        lines.append(f"{path_name} = {print_path(endpoint.route)}")
        lines.append("")

    # Parameters
    for i, endpoint in enumerate(api.paths):
        for j, param in enumerate(endpoint.parameters):
            param_name = f"Param{i}x{j}"
            lines.append(f"{param_name} : Parameter")
            lines.append(f"{param_name} = {print_parameter(param)}")
            lines.append("")

    # Responses
    for i, endpoint in enumerate(api.paths):
        resp_name = f"Responses{i}"
        responses_str = agda_list(
            [print_response(r) for r in endpoint.responses]
        )

        lines.append(f"{resp_name} : List Response")
        lines.append(f"{resp_name} = {responses_str}")
        lines.append("")

    # Endpoints
    for i, endpoint in enumerate(api.paths):
        endpoint_name = f"Endpoint{i}"
        path_name = f"Path{i}"
        resp_name = f"Responses{i}"

        params = [
            f"Param{i}x{j}"
            for j in range(len(endpoint.parameters))
        ]
        params_str = agda_list(params)

        lines.append(f"{endpoint_name} : Endpoint")
        lines.append(
            " ".join([
                f"{endpoint_name} = record {{",
                f"route = {path_name} ;",
                f"method = {endpoint.method} ;",
                f"parameters = {params_str} ;",
                f"body = {print_body(endpoint.body)} ;",
                f"responses = {resp_name} }}"
            ])
        )
        lines.append("")

    # Final API
    endpoint_names = [f"Endpoint{i}" for i in range(len(api.paths))]
    endpoints_str = agda_list(endpoint_names)

    components_str = agda_list(
        [f'("{name}" , {name})' for name, _ in api.components]
    )

    lines.append("GeneratedAPI : API")
    lines.append(
        f"GeneratedAPI = record {{ paths = {endpoints_str} ; components = {components_str} }}"
    )

    return "\n".join(lines)
