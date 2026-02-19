from dsl_ast import API, Schema


def agda_list(items: list[str]) -> str:
    if not items:
        return "[]"

    result = items[-1]
    for item in reversed(items[:-1]):
        result = f"{item} :: {result}"

    return f"{result} :: []"

def print_schema(schema: Schema) -> str:
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

def print_api_module(api: API, module_name: str) -> str:
    lines = []

    lines.append(f"module {module_name} where")
    lines.append("")
    lines.append("open import All")
    lines.append("")

    # Components
    for name, schema in api.components:
        lines.append(f"{name} : Schema")
        lines.append(f"{name} = {print_schema(schema)}")
        lines.append("")

    lines.append("-- Endpoints not yet printed")
    lines.append("")

    return "\n".join(lines)
