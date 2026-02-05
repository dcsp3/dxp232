# Planning Semantics

### The Goal

So far we have defined:

- **Syntax**: enough structure to write OpenAPI-shaped specifications.
- **Well-formedness**: rules out specifications that are structurally incoherent (e.g. “array schemas with no items”, required fields not present in properties, mismatched paths/params).

What’s still missing is *meaning*. The semantic layer is where we stop talking about well-shaped documents and start talking about what an API actually promises to clients and expects from them.

More precisely:

> We need a definition of what an API specification means, and a principled notion of safe evolution derived from that meaning.

This is what will let us classify changes as safe or breaking in a way that supports proofs, rather than relying on arbitrary “diff rules”.

---

### Why Equality Is Not Enough

In our earlier [naive approach](./oldSemantics.md) to compatibility, we treated two specifications as compatible when they are structurally equal (or equal up to reordering). While that’s a useful starting point, it doesn’t model real API evolution.

For example, some safe changes can be:
- adding an optional field to a response object (clients can ignore it),
- accepting a broader request shape (servers become more permissive).

And some breaking changes can be:
- removing a required field from a response object,
- making a previously optional request field required (old clients won’t send it).

So instead of treating compatibility as “same structure”, the plan is to treat it as a **semantic refinement relation** (a preorder): the new version is compatible with the old one if it preserves the old contract.

---

### Variance as a Semantic Principle

The key observation is that requests and responses behave differently under evolution:

- Responses are produced by the server and consumed by the client.
- Requests are produced by the client and consumed by the server.

So “safe evolution” depends on *who* is observing the change. We can capture this using [variance](./variance.md):

```agda
data Variance : Set where
  Co Contra
```

- `Co` is used for response positions (client-observed).
- `Contra` is used for request positions (server-observed).

Contravariance is not implemented as a separate rule set. It is defined by flipping the direction of refinement, so we only write the core refinement rules once.

This approach aims to give us:
- safe extensions and breaking changes (without requiring exact equality),
- a principled explanation of request/response asymmetry,
- and drift detection stated against semantic preservation rather than syntactic mismatch.

---

## Step-by-step Plan

### Step 1: Choose the semantic object

Before we talk about compatibility or drift, we need to pick what semantic object we’re actually going to reason about.

A fully denotational approach would interpret each schema as a set of JSON values. That’s clean in theory, but it forces us to build a whole JSON model and prove a bunch of meta-lemmas before we even get to compatibility.

Instead, the plan is to treat meaning operationally: a schema is characterised by what it allows or forbids in an observable way. That naturally leads to a refinement relation where one schema safely refines another when it can replace it without breaking the relevant party.

---

### Step 2: Define schema refinement

The core semantic judgement is a variance-aware refinement relation on schemas:

```agda
Schema⊑ : Variance → Schema → Schema → Set
```

We read `Schema⊑ v old new` as:
>under variance v, new is a safe replacement for old.

This allows us to capture replaceability without requiring structural equality.

Refinement is defined by structural recursion on well-formedness proofs, so ill-formed cases are ruled out by construction.

At a high level:
- primitives refine by widening rules (at minimum equality),
- arrays refine via refinement of their item schemas,
- objects handle:
    - recursive refinement of properties,
    - variance-sensitive treatment of required fields,
    - allowance of extra optional fields in covariant (response) positions.

This forces the request/response story into the formal rules.

---

### Step 3: Prove the algebraic backbone

Prove that refinement is:
- reflexive
- transitive

These properties matter because they enable composition of changes and later multi-step evolution arguments. The proofs are by structural induction.

---

### Step 4: Lift refinement to endpoints

Define what it means for endpoints to be compatible:
- routes + methods are treated as invariant (for now),
- parameters refine contravariantly,
- request bodies refine contravariantly,
- response schemas refine covariantly.

This takes us from "two endpoints are equal if their lists match" to "new endpoint is safe for old clients/servers"

---

### Step 5: Operational evolution (secondary layer)

After the semantic preorder is defined, introduce small-step evolution rules representing common API changes (add optional response field, add new response status, relax request requirement, etc.) and prove each step preserves refinement.

This gives a clean bridge from:

- a semantic notion of safety (refinement), to
- a human-friendly evolution calculus (steps),

and supports the theorem: reachability implies compatibility.

---

### Step 6: Drift witnesses and the main theorem

Now the drift result becomes meaningful. Drift is not “lists differ”, it's “a refinement obligation fails” (required added, enum narrowed, type tightened, etc.)

Then prove:
- drift witness ⇒ not compatible

This makes drift detection meaningful: it points to a specific broken semantic contract.

---

### Disclaimer: Scope and Flexibility

This document outlines the *intended* structure of the semantic layer and the order in which its components are developed. It should be read as a guiding plan rather than a fixed specification.

As the formalisation progresses, some steps may be refined, reordered, or extended in response to proof obligations, design trade-offs, or feedback. The core commitments of the approach remain unchanged: compatibility is defined semantically via variance-aware refinement, and drift is characterised as failure of semantic preservation rather than syntactic mismatch.