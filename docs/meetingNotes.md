# Meeting Notes

# Semester 1

---

## Week 1 (30/09)
- Group meeting with all students - everyone shared their initial project ideas.  
- Started thinking about what direction I want to take mine in.  

---

## Week 2 (07/10)
- Pitched the [idea](./projectIdea.md) of building a dependently-typed language for REST APIs.  
- Supervisor wasn’t totally sure what the language would look like yet, told me to refine it and make it more concrete.  

---

## Week 3 (14/10)
- Talked about the difference between shallow and deep embeddings.  
  - Deep = something that could actually generate TS/Python code later.  
- Need to figure out what the language looks like and what properties I actually want to prove.  
- Started exploring another similar idea of formalising a subset of TypeScript in Agda using dependent types.  

---

## Week 4 (21/10)
- Focused on how to describe REST APIs using dependent types.  
- Still not totally clear on a few things:  
  - How to define *client-server drift* properly.  
  - What the syntax and scope of the language should be.  
  - How users would actually interact with it.  
  - How complex the proofs might get.  
- Plan is to pick one property and try to formalise it first.  
- Supervisor also suggested looking at the **CompCert** paper for ideas, as well as similar projects by previous students.

---

## Week 5 (28/10)  
- The language is clearer and makes much more sense after showing the minimal syntax and semantics files.
- Talked about:  
  - Simplifying schemas (dropping datatypes).  
  - Subtypes vs subsets when handling requests.  
  - Keeping semantics focused on the client-server interaction.  
- Need to define what it means for two endpoints to be compatible, then make that a type-level condition in the language itself.  
- Would be useful to prove that compatibility is *decidable*, which would allow me to always show if two endpoints in my language are compatible or not.
- The final API structure might look something like this: `API = (Endpoint_c , Endpoint_s) × Compatible Endpoint_c Endpoint_s`.
- Complexity in the project can be added from interpreting this code into TS.

---

## Week 6 (04/11)
- Fixed concrete schema types.  
- Started thinking about semantics as sets of client-server interactions.  
- Looked into the **OpenAPI 3.1.1** spec as a reference point for defining how requests/responses should behave - need to do more research on the spec itself.  
- Plan now is to formalise a small, useful subset of OpenAPI inside the language to ground everything more concretely.  

---

## Week 7 (11/11)

- The semantics should be in terms of how the users behave
- Explore authentication/authorisation - something to prove about security of endpoints
- Could have some sort of 'guarantee' about endpoints/interactions being secure
- [Information flow](https://en.wikipedia.org/wiki/Information_flow_(information_theory))
- Proving [non-interferance](https://en.wikipedia.org/wiki/Non-interference_(security))
- First try the refinement proof, then later on we can extend semantics   

## Weeks 8-10

- Regular catchups but more focus on other module deadlines

---
---


# Semester 2

---

## Week 1 (20/1)

- Explained the idea of well-formedness, why I defined it and how it sits between syntax and semantics
- Discussed how semantics should only apply to well-formed APIs
- Also explained future idea of translation + demonstrating real life case-studies 
- Supervisor suggested defining semantics in an operational way
- Idea to model API evolution as a sequence of steps (small-step semantics)
- Compatibility = existence of a sequence of valid steps from API A to API B (transitive closure)
- Leads naturally to a rule-based notion of API evolution
- Would be helpful to write a document and create a plan for semantics

---

## Week 2 (27/1)

No meeting

---

## Week 3 (3/2)

- Updated on progress with [schema refinement](../agda/Semantics/SchemaRefinement.lagda.md) and current proof structure
- Current refinement relation essentially a big-step view of compatibility (directly relating old and new schemas, rather than via intermediate steps)
- Discussed the need for small, concrete examples of breaking or incompatible changes
- Idea to define explicit schema transformation functions for breaking changes and prove they produce incompatibility under the refinement relation
- Plan to come up with a clear list of things to prove going forward
- Deeper dive into the Agda code next meeting

---
