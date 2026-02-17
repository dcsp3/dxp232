from dsl_ast import Schema, API

ALLOWED_BASE_TYPES = {
    "integer",
    "string",
    "boolean",
    "number",
    "object",
    "array",
}


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

def translate_api(spec: dict) -> API:
    components_dict = spec.get("components", {}).get("schemas", {})

    translated_components = []

    for name, raw_schema in components_dict.items():
        translated_schema = translate_schema(raw_schema, components_dict)
        translated_components.append((name, translated_schema))

    # will implement endpoint translation next
    translated_paths = []

    return API(
        paths=translated_paths,
        components=translated_components,
    )