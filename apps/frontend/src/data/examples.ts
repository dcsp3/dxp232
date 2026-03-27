export const oldApiExample = `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
  /health:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`;

export const newApiExample = `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`;


export type ExampleCategory = "compatible" | "breaking" | "input-error";

export interface ExamplePair {
  id: string;
  title: string;
  description: string;
  change: string;
  category: ExampleCategory;
  expectedTag: string;
  old: string;
  new: string;
}


const compatAddOptionalProperty: ExamplePair = {
  id: "compat-add-optional-property",
  title: "Add optional schema property",
  description:
    "New optional field added to a response schema. Existing clients that don't use it are unaffected.",
  change: "User gains optional email: string (not in required list)",
  category: "compatible",
  expectedTag: "COMPAT_OK",
  old: `openapi: 3.1.0
paths:
  /users:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
        name:
          type: string
      required:
        - id
        - name`,
  new: `openapi: 3.1.0
paths:
  /users:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
        name:
          type: string
        email:
          type: string
      required:
        - id
        - name`,
};

const compatAddEndpoint: ExamplePair = {
  id: "compat-add-endpoint",
  title: "Add new endpoint",
  description:
    "New GET /health route added. All existing paths and schemas stay the same.",
  change: "/health GET added alongside /ping",
  category: "compatible",
  expectedTag: "COMPAT_OK",
  old: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Ping:
      type: object
      properties:
        healthy:
          type: integer
      required:
        - healthy`,
  new: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
  /health:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Ping:
      type: object
      properties:
        healthy:
          type: integer
      required:
        - healthy`,
};

const compatAddComponent: ExamplePair = {
  id: "compat-add-component",
  title: "Add new component schema",
  description:
    "New Session schema introduced. Existing User schema and all paths are untouched.",
  change: "Session schema added; User and all paths unchanged",
  category: "compatible",
  expectedTag: "COMPAT_OK",
  old: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id
    Session:
      type: object
      properties:
        token:
          type: string
      required:
        - token`,
};


const breakingEndpointRemoved: ExamplePair = {
  id: "breaking-endpoint-removed",
  title: "Endpoint removed",
  description:
    "GET /users exists in the old API but is gone from the new one. Clients calling it will get a 404.",
  change: "/users GET removed",
  category: "breaking",
  expectedTag: "COMPAT_ERR:ENDPOINT_REMOVED",
  old: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
  /users:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};

const breakingResponseTypeChanged: ExamplePair = {
  id: "breaking-response-type-changed",
  title: "Response primitive type changed",
  description:
    "GET /status 200 body changed from string to integer. Clients that parse the response as a string will break.",
  change: "GET /status 200 response: string → integer",
  category: "breaking",
  expectedTag: "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PRIMITIVE_CHANGED",
  old: `openapi: 3.1.0
paths:
  /status:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Info:
      type: object
      properties:
        version:
          type: string
      required:
        - version`,
  new: `openapi: 3.1.0
paths:
  /status:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: integer
components:
  schemas:
    Info:
      type: object
      properties:
        version:
          type: string
      required:
        - version`,
};

const breakingNewRequiredParameter: ExamplePair = {
  id: "breaking-new-required-parameter",
  title: "New required query parameter",
  description:
    "GET /search now requires a query param q. Old clients that omit it will get a validation error.",
  change: "GET /search: required query param q added",
  category: "breaking",
  expectedTag: "COMPAT_ERR:ENDPOINT_NEW_REQUIRED_PARAMETER",
  old: `openapi: 3.1.0
paths:
  /search:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Result:
      type: object
      properties:
        count:
          type: integer
      required:
        - count`,
  new: `openapi: 3.1.0
paths:
  /search:
    get:
      parameters:
        - name: q
          in: query
          required: true
          schema:
            type: string
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Result:
      type: object
      properties:
        count:
          type: integer
      required:
        - count`,
};

const breakingComponentShapeMismatch: ExamplePair = {
  id: "breaking-component-shape-mismatch",
  title: "Component schema shape changed",
  description:
    "Token was an object with a value field; the new API makes it a bare integer. Any client that unpacks the object breaks.",
  change: "Token: {value: string} → integer",
  category: "breaking",
  expectedTag: "COMPAT_ERR:COMPONENT_SCHEMA_SHAPE_MISMATCH",
  old: `openapi: 3.1.0
paths:
  /auth:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Token:
      type: object
      properties:
        value:
          type: string
      required:
        - value`,
  new: `openapi: 3.1.0
paths:
  /auth:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Token:
      type: integer`,
};

const breakingRequiredFieldRemoved: ExamplePair = {
  id: "breaking-required-field-removed",
  title: "Required field removed from component",
  description:
    "User previously required id and email. The new version only requires id, so email may no longer appear in responses.",
  change: "User required: [id, email] → [id]",
  category: "breaking",
  expectedTag: "COMPAT_ERR:COMPONENT_SCHEMA_REQUIRED_FIELD_REMOVED",
  old: `openapi: 3.1.0
paths:
  /users:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
        email:
          type: string
      required:
        - id
        - email`,
  new: `openapi: 3.1.0
paths:
  /users:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
        email:
          type: string
      required:
        - id`,
};

const breakingComponentPropertyDrift: ExamplePair = {
  id: "breaking-component-property-drift",
  title: "Component property type changed",
  description:
    "Product.price was a string (e.g. \"9.99\") and is now an integer. Clients that deserialise it as a string will fail.",
  change: "Product.price: string → integer",
  category: "breaking",
  expectedTag: "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_DRIFT",
  old: `openapi: 3.1.0
paths:
  /products:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Product:
      type: object
      properties:
        id:
          type: integer
        price:
          type: string
      required:
        - id
        - price`,
  new: `openapi: 3.1.0
paths:
  /products:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Product:
      type: object
      properties:
        id:
          type: integer
        price:
          type: integer
      required:
        - id
        - price`,
};

const breakingComponentRemoved: ExamplePair = {
  id: "breaking-component-removed",
  title: "Component schema removed",
  description:
    "The Error schema was available in the old API. The new API drops it entirely.",
  change: "Error component schema removed",
  category: "breaking",
  expectedTag: "COMPAT_ERR:COMPONENT_REMOVED",
  old: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id
    Error:
      type: object
      properties:
        code:
          type: integer
        message:
          type: string
      required:
        - code
        - message`,
  new: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};


const breakingParameterRemoved: ExamplePair = {
  id: "breaking-parameter-removed",
  title: "Query parameter removed",
  description:
    "GET /items had an optional filter query parameter. The new API drops it entirely, so clients that send it get no acknowledgement and any server logic that relied on it is gone.",
  change: "GET /items: optional query param filter removed",
  category: "breaking",
  expectedTag: "COMPAT_ERR:ENDPOINT_PARAMETER_REMOVED",
  old: `openapi: 3.1.0
paths:
  /items:
    get:
      parameters:
        - name: filter
          in: query
          required: false
          schema:
            type: string
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Item:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /items:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Item:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};

const breakingParameterTypeChanged: ExamplePair = {
  id: "breaking-parameter-type-changed",
  title: "Query parameter type changed",
  description:
    "GET /reports accepted page as a string. The new API changes it to an integer. Clients sending string values will now fail schema validation.",
  change: "GET /reports: page param type string → integer",
  category: "breaking",
  expectedTag: "COMPAT_ERR:ENDPOINT_PARAMETER_SCHEMA_CHANGED",
  old: `openapi: 3.1.0
paths:
  /reports:
    get:
      parameters:
        - name: page
          in: query
          required: false
          schema:
            type: string
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Report:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /reports:
    get:
      parameters:
        - name: page
          in: query
          required: false
          schema:
            type: integer
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Report:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};

const breakingResponseRequiredFieldRemoved: ExamplePair = {
  id: "breaking-response-required-field-removed",
  title: "Required field removed from response body",
  description:
    "GET /orders 200 response was an object with id and status both required. The new API demotes status to optional, so clients that always expected it will break.",
  change: "GET /orders response object: required status removed",
  category: "breaking",
  expectedTag: "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_REQUIRED_FIELD_REMOVED",
  old: `openapi: 3.1.0
paths:
  /orders:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: object
                properties:
                  id:
                    type: integer
                  status:
                    type: string
                required:
                  - id
                  - status
components:
  schemas:
    Empty:
      type: object
      properties:
        x:
          type: integer
      required:
        - x`,
  new: `openapi: 3.1.0
paths:
  /orders:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: object
                properties:
                  id:
                    type: integer
                  status:
                    type: string
                required:
                  - id
components:
  schemas:
    Empty:
      type: object
      properties:
        x:
          type: integer
      required:
        - x`,
};


const breakingPropertyRemoved: ExamplePair = {
  id: "breaking-property-removed",
  title: "Property removed from component",
  description:
    "Order had an id and a reference field. The new API drops reference from the schema altogether. Clients that read it will no longer find it.",
  change: "Order.reference property removed entirely",
  category: "breaking",
  expectedTag: "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_REMOVED",
  old: `openapi: 3.1.0
paths:
  /orders:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Order:
      type: object
      properties:
        id:
          type: integer
        reference:
          type: string
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /orders:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Order:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};

const breakingComponentPrimitiveChanged: ExamplePair = {
  id: "breaking-component-primitive-changed",
  title: "Component schema primitive type changed",
  description:
    "The Cursor schema was a string (e.g. a pagination token). The new API changes it to an integer. Any client that treats it as a string breaks.",
  change: "Cursor schema: string → integer",
  category: "breaking",
  expectedTag: "COMPAT_ERR:COMPONENT_SCHEMA_PRIMITIVE_CHANGED",
  old: `openapi: 3.1.0
paths:
  /items:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Cursor:
      type: string`,
  new: `openapi: 3.1.0
paths:
  /items:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Cursor:
      type: integer`,
};


const inputErrorPathParamNotRequired: ExamplePair = {
  id: "input-path-param-not-required",
  title: "Path parameter not marked required",
  description:
    "OpenAPI mandates that path parameters are always required: true. The old spec sets required: false on id, so the checker rejects it before doing any comparison.",
  change: "/users/{id}: path param id has required: false",
  category: "input-error",
  expectedTag: "WF_ERR:API_ENDPOINT_PATH_PARAM_NOT_REQUIRED",
  old: `openapi: 3.1.0
paths:
  /users/{id}:
    get:
      parameters:
        - name: id
          in: path
          required: false
          schema:
            type: integer
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /users/{id}:
    get:
      parameters:
        - name: id
          in: path
          required: true
          schema:
            type: integer
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};

const inputErrorDuplicateParameters: ExamplePair = {
  id: "input-duplicate-parameters",
  title: "Duplicate query parameters",
  description:
    "GET /search declares q twice with conflicting types. The spec fails the well-formedness check before any compatibility comparison runs.",
  change: "GET /search: q declared twice (string + integer)",
  category: "input-error",
  expectedTag: "WF_ERR:API_ENDPOINT_DUPLICATE_PARAMETERS",
  old: `openapi: 3.1.0
paths:
  /search:
    get:
      parameters:
        - name: q
          in: query
          required: true
          schema:
            type: string
        - name: q
          in: query
          required: true
          schema:
            type: integer
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Result:
      type: object
      properties:
        count:
          type: integer
      required:
        - count`,
  new: `openapi: 3.1.0
paths:
  /search:
    get:
      parameters:
        - name: q
          in: query
          required: true
          schema:
            type: string
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Result:
      type: object
      properties:
        count:
          type: integer
      required:
        - count`,
};

const inputErrorOrphanPathParameter: ExamplePair = {
  id: "input-orphan-path-parameter",
  title: "Orphan path parameter",
  description:
    "GET /users declares a path parameter 'id', but the route '/users' does not contain an '{id}' placeholder. The specification fails the well-formedness check.",
  change: "GET /users: orphaned path parameter 'id'",
  category: "input-error",
  expectedTag: "WF_ERR:API_ENDPOINT_PATH_ILL_FORMED",
  old: `openapi: 3.1.0
paths:
  /users:
    get:
      parameters:
        - name: id
          in: path
          required: true
          schema:
            type: integer
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
  new: `openapi: 3.1.0
paths:
  /users:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
      required:
        - id`,
};

const inputErrorDuplicateStatuses: ExamplePair = {
  id: "input-duplicate-statuses",
  title: "Duplicate response status codes",
  description:
    "GET /ping declares a 200 response twice. The spec fails the well-formedness check: a response status code must appear at most once per operation.",
  change: "Old API: GET /ping has 200 status declared twice",
  category: "input-error",
  expectedTag: "WF_ERR:API_ENDPOINT_DUPLICATE_STATUSES",
  old: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
        "200":
          description: also ok
          content:
            application/json:
              schema:
                type: integer
components:
  schemas:
    Health:
      type: object
      properties:
        healthy:
          type: integer
      required:
        - healthy`,
  new: `openapi: 3.1.0
paths:
  /ping:
    get:
      responses:
        "200":
          description: ok
          content:
            application/json:
              schema:
                type: string
components:
  schemas:
    Health:
      type: object
      properties:
        healthy:
          type: integer
      required:
        - healthy`,
};


export const EXAMPLES: ExamplePair[] = [
  compatAddOptionalProperty,
  compatAddEndpoint,
  compatAddComponent,
  breakingEndpointRemoved,
  breakingResponseTypeChanged,
  breakingNewRequiredParameter,
  breakingParameterRemoved,
  breakingParameterTypeChanged,
  breakingResponseRequiredFieldRemoved,
  breakingComponentShapeMismatch,
  breakingRequiredFieldRemoved,
  breakingComponentPropertyDrift,
  breakingPropertyRemoved,
  breakingComponentPrimitiveChanged,
  breakingComponentRemoved,
  inputErrorPathParamNotRequired,
  inputErrorDuplicateParameters,
  inputErrorOrphanPathParameter,
  inputErrorDuplicateStatuses,
];


