from dataclasses import dataclass
from typing import List, Optional, Tuple

# Base
Base = str
# Allowed: "integer", "string", "boolean", "number", "object", "array"

# Schema
@dataclass
class Schema:
    type: Base
    properties: List[Tuple[str, "Schema"]]
    required: List[str]
    items: Optional["Schema"]

# Schema ref
@dataclass
class SchemaRef:
    name: str

# Parameter
@dataclass
class Parameter:
    name: str
    location: str  # "path" or "query"
    required: bool
    schema: Base
    
# Path
@dataclass
class PathSegment:
    kind: str  # "lit" or "param"
    value: str

@dataclass
class Path:
    segments: List[PathSegment]
    
# Body
@dataclass
class Body:
    kind: str  # "NoBody", "NoBodyD", "HasBody", "HasBodyU", "HasBodyP"
    schema: Optional[Schema]
    
# Response
@dataclass
class Response:
    status: str  # "OK", "BadRequest", "NotFound", "NoContent"
    schema: Schema
    
# Endpoint
@dataclass
class Endpoint:
    route: Path
    method: str  # "GET", "POST", "PUT", "DELETE", "PATCH"
    parameters: List[Parameter]
    body: Body
    responses: List[Response]
    
# API
@dataclass
class API:
    paths: List[Endpoint]
    components: List[Tuple[str, Schema]]
