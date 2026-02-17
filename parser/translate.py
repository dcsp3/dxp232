from dsl_ast import Schema

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


def translate_schema(raw: dict) -> Schema:
    if not isinstance(raw, dict):
        raise TranslationError("Schema must be an object.")

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

    raise TranslationError(
        f"Base type '{base_type}' not supported yet"
    )
