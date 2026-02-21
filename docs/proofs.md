## Results and proof goals

| Area | Result | Statement | Relevance |
|-----|--------|-----------|-----------|
| Schema refinement | Preorder structure | Schema refinement is reflexive and transitive over well-formed schemas | Provides a compositional notion of safe schema evolution |
| Endpoint refinement | Preorder structure | Endpoint refinement is reflexive and transitive, reusing schema refinement | Captures safe evolution of request/response behaviour |
| API refinement | Preorder structure | One API safely refines another by structurally refining its components and endpoints | Lifts refinement to whole API specifications |
| Compatibility | Compatibility via API refinement | Compatibility is defined using API refinement | Central definition of backward-compatible API evolution |
| Equivalence | Induced equivalence relation | Two APIs are equivalent iff each refines the other (A ⊑ B ∧ B ⊑ A) | Provides a principled notion of API sameness and enables structural classification of change |
| Decidability | Decidable compatibility | Compatibility between two APIs is a yes/no decision procedure | Makes compatibility mechanically checkable |
| Drift | Drift theorem | Any concrete witness of drift implies incompatibility | Shows incompatibility is observable and constructive |
| Breaking changes | Breaking-change examples | Concrete API transformations that induce drift and violate compatibility | Grounds the drift theorem in explicit, checkable examples |
| Case studies | Good vs bad evolution | Small API evolutions classified as compatible or incompatible | Demonstrates practical usefulness of the theory |


