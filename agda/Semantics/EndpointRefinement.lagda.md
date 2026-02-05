# Endpoint Refinement

We have defined refinement at the level of schemas and shown that it is reflexive and transitive. The next step is to lift this notion to endpoints.

Intuitively, one endpoint safely refines another if it preserves the observable behaviour expected by existing clients. This is determined by how the endpoint handles requests and responses.

- Request-facing components are checked **contravariantly**: a new endpoint is safe if it accepts at least the requests that were previously accepted.

- Response-facing components are checked **covariantly**: a new endpoint is safe if it returns responses that refine those expected by clients.

Rather than defining new refinement rules from scratch, endpoint refinement is defined by reusing schema refinement together with variance. Structural aspects of endpoints, such as the HTTP method and route, are required to remain unchanged.

The remainder of this file formalises this judgement and establishes its basic properties.

---
