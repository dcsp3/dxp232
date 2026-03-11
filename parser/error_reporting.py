WF_ERROR_MESSAGES = {
    "API_DUPLICATE_COMPONENTS": "Duplicate component names found.",
    "API_DUPLICATE_ENDPOINTS": "Duplicate endpoint (path, method) pairs found.",
    "API_ENDPOINT_PATH_ILL_FORMED": "An endpoint has an ill-formed path/parameter alignment.",
    "API_ENDPOINT_PARAMETER_ILL_FORMED": "An endpoint has an ill-formed parameter.",
    "API_ENDPOINT_DUPLICATE_PARAMETERS": "An endpoint has duplicate parameters.",
    "API_ENDPOINT_DUPLICATE_STATUSES": "An endpoint has duplicate response statuses.",
    "API_COMPONENT_SCHEMA_PRIM_HAS_ITEMS": "A component primitive schema incorrectly has an items field.",
    "API_COMPONENT_SCHEMA_PRIM_HAS_PROPERTIES": "A component primitive schema incorrectly has properties.",
    "API_COMPONENT_SCHEMA_PRIM_HAS_REQUIRED": "A component primitive schema incorrectly has required fields.",
    "API_COMPONENT_SCHEMA_ARRAY_MISSING_ITEMS": "A component array schema is missing items.",
    "API_COMPONENT_SCHEMA_ARRAY_ITEM_ILL_FORMED": "A component array item schema is ill-formed.",
    "API_COMPONENT_SCHEMA_ARRAY_HAS_PROPERTIES": "A component array schema incorrectly has properties.",
    "API_COMPONENT_SCHEMA_ARRAY_HAS_REQUIRED": "A component array schema incorrectly has required fields.",
    "API_COMPONENT_SCHEMA_OBJECT_HAS_ITEMS": "A component object schema incorrectly has items.",
    "API_COMPONENT_SCHEMA_OBJECT_PROPERTY_ILL_FORMED": "A component object has an ill-formed property schema.",
    "API_COMPONENT_SCHEMA_OBJECT_MISSING_REQUIRED": "A component object requires a field not present in properties.",
    "API_COMPONENT_SCHEMA_OBJECT_DUPLICATE_PROPERTIES": "A component object has duplicate property keys.",
    "API_COMPONENT_SCHEMA_OBJECT_DUPLICATE_REQUIRED": "A component object has duplicate required entries.",
    "API_ENDPOINT_BODY_SCHEMA_PRIM_HAS_ITEMS": "Endpoint body primitive schema incorrectly has items.",
    "API_ENDPOINT_BODY_SCHEMA_PRIM_HAS_PROPERTIES": "Endpoint body primitive schema incorrectly has properties.",
    "API_ENDPOINT_BODY_SCHEMA_PRIM_HAS_REQUIRED": "Endpoint body primitive schema incorrectly has required fields.",
    "API_ENDPOINT_BODY_SCHEMA_ARRAY_MISSING_ITEMS": "Endpoint body array schema is missing items.",
    "API_ENDPOINT_BODY_SCHEMA_ARRAY_ITEM_ILL_FORMED": "Endpoint body array item schema is ill-formed.",
    "API_ENDPOINT_BODY_SCHEMA_ARRAY_HAS_PROPERTIES": "Endpoint body array schema incorrectly has properties.",
    "API_ENDPOINT_BODY_SCHEMA_ARRAY_HAS_REQUIRED": "Endpoint body array schema incorrectly has required fields.",
    "API_ENDPOINT_BODY_SCHEMA_OBJECT_HAS_ITEMS": "Endpoint body object schema incorrectly has items.",
    "API_ENDPOINT_BODY_SCHEMA_OBJECT_PROPERTY_ILL_FORMED": "Endpoint body object has an ill-formed property schema.",
    "API_ENDPOINT_BODY_SCHEMA_OBJECT_MISSING_REQUIRED": "Endpoint body object requires a field not present in properties.",
    "API_ENDPOINT_BODY_SCHEMA_OBJECT_DUPLICATE_PROPERTIES": "Endpoint body object has duplicate property keys.",
    "API_ENDPOINT_BODY_SCHEMA_OBJECT_DUPLICATE_REQUIRED": "Endpoint body object has duplicate required entries.",
    "API_ENDPOINT_RESPONSE_SCHEMA_PRIM_HAS_ITEMS": "Endpoint response primitive schema incorrectly has items.",
    "API_ENDPOINT_RESPONSE_SCHEMA_PRIM_HAS_PROPERTIES": "Endpoint response primitive schema incorrectly has properties.",
    "API_ENDPOINT_RESPONSE_SCHEMA_PRIM_HAS_REQUIRED": "Endpoint response primitive schema incorrectly has required fields.",
    "API_ENDPOINT_RESPONSE_SCHEMA_ARRAY_MISSING_ITEMS": "Endpoint response array schema is missing items.",
    "API_ENDPOINT_RESPONSE_SCHEMA_ARRAY_ITEM_ILL_FORMED": "Endpoint response array item schema is ill-formed.",
    "API_ENDPOINT_RESPONSE_SCHEMA_ARRAY_HAS_PROPERTIES": "Endpoint response array schema incorrectly has properties.",
    "API_ENDPOINT_RESPONSE_SCHEMA_ARRAY_HAS_REQUIRED": "Endpoint response array schema incorrectly has required fields.",
    "API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_HAS_ITEMS": "Endpoint response object schema incorrectly has items.",
    "API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_PROPERTY_ILL_FORMED": "Endpoint response object has an ill-formed property schema.",
    "API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_MISSING_REQUIRED": "Endpoint response object requires a field not present in properties.",
    "API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_DUPLICATE_PROPERTIES": "Endpoint response object has duplicate property keys.",
    "API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_DUPLICATE_REQUIRED": "Endpoint response object has duplicate required entries.",
}


TRANSLATION_ERROR_MESSAGES = {
    "SCHEMA_UNKNOWN_FIELD": "A schema uses a keyword outside the supported subset.",
    "SCHEMA_UNEXPECTED_FIELD": "A schema uses a field that is incompatible with its declared type.",
    "SCHEMA_NOT_OBJECT": "A schema value must be an object.",
    "REF_UNSUPPORTED_FORMAT": "A schema reference uses an unsupported format.",
    "REF_SCHEMA_NOT_FOUND": "A schema reference points to a missing component.",
    "SCHEMA_MISSING_TYPE": "A schema is missing its type.",
    "OBJECT_PROPERTIES_NOT_OBJECT": "An object schema has a non-object properties field.",
    "OBJECT_REQUIRED_NOT_LIST": "An object schema has a non-list required field.",
    "ARRAY_MISSING_ITEMS": "An array schema is missing items.",
    "SCHEMA_UNSUPPORTED_TYPE": "A schema uses an unsupported base type.",
    "PATH_INVALID_FORMAT": "A path string has an invalid format.",
    "PATH_LEVEL_PARAMETERS_UNSUPPORTED": "Path-level parameters are not supported in this subset.",
    "REQUEST_BODY_MISSING": "An operation requiring a body is missing requestBody.",
    "REQUEST_BODY_MISSING_JSON_CONTENT": "A request body is missing application/json content.",
    "REQUEST_BODY_MISSING_SCHEMA": "A request body is missing its schema.",
    "BODY_UNSUPPORTED_METHOD": "A method/body combination is unsupported.",
    "METHOD_UNSUPPORTED": "An HTTP method is unsupported.",
    "PARAMETER_UNSUPPORTED_LOCATION": "A parameter location is unsupported.",
    "PARAMETER_MISSING_SCHEMA": "A parameter is missing its schema.",
    "PARAMETER_SCHEMA_MISSING_TYPE": "A parameter schema is missing its type.",
    "PARAMETER_NON_PRIMITIVE": "A parameter schema must be primitive.",
    "PATH_PARAMETER_NOT_REQUIRED": "A path parameter must be marked required.",
    "STATUS_UNSUPPORTED": "A response status code is unsupported.",
    "RESPONSE_MISSING_JSON_CONTENT": "A response is missing application/json content.",
    "RESPONSE_MISSING_SCHEMA": "A response is missing its schema.",
}


COMPAT_ERROR_MESSAGES = {
    "COMPONENT_REMOVED": "A component required by the old API is missing in the new API.",
    "COMPONENT_DRIFT": "A shared component changed incompatibly.",
    "ENDPOINT_REMOVED": "An endpoint present in the old API is missing in the new API.",
    "ENDPOINT_DRIFT": "A shared endpoint changed incompatibly.",
}


def format_context_parts(*pairs: tuple[str, str]) -> str:
    parts = []
    for key, value in pairs:
        if key and value:
            parts.append(f"{key}={value}")
    return " ".join(parts)