# Semantics

In this file, I try define a *semantic* notion of compatibility between two REST endpoints
and formally prove what I call the **Drift Theorem**, which states that:

> "If there exists a witness of drift between two endpoints,
> then those endpoints cannot be semantically compatible."


```agda
module Semantics where

open import Prelude
open import MinimalSyntax
```

## Lookup Function
This function interprets a syntactic list of `(Status, Schema)` pairs as a semantic mapping from status codes to payload schemas.

It is used to reason about how a client and server “see” the meaning of an endpoint.

```agda
lookup : Status → List RespCase → Maybe Schema
lookup OK []                            = nothing
lookup OK (Case OK x :: xs)             = just x
lookup OK (Case NotFound _ :: xs)       = lookup OK xs

lookup NotFound []                      = nothing
lookup NotFound (Case OK x :: xs)       = lookup NotFound xs
lookup NotFound (Case NotFound x :: xs) = just x
```

The intuition:
- `lookup` extracts the schema corresponding to a given HTTP status
- If no case matches, it returns `nothing`

This way we give a semantic meaning to the list representation.

## Compatibility

Two endpoints are **Compatible** if:
1. They use the same HTTP method (`GET`, `POST`, etc.), **and**
2. For every possible `Status`, both endpoints map that status to the same `Maybe Schema` value

This captures the idea that client and server *agree* on structure and behaviour.

```agda
Compatible : Endpoint → Endpoint → Set
Compatible client server = methods-equal × response-equal
  where
    methods-equal  = Endpoint.method client ≡ Endpoint.method server
    response-equal = ∀ st → lookup st (Endpoint.responses client)
                          ≡ lookup st (Endpoint.responses server)
```

This gives a semantic meaning to compatibility. Endpoints might differ syntactically (e.g., different paths or order of cases)
but still be semantically identical.


# Drift Theorem

Now that we know what being compatible means for a client and server, we can move on to proving our drift theorem, stated in Agda as:


### drift-theorem : ∀ {client server} → DriftWitness client server → ¬ Compatible client server


i.e. “If we can produce evidence (a drift witness) showing that some part of the client and server differ, then they cannot be compatible.”

Client-server drift means that there exists at least one specific point of disagreement between the client and the server.


## Drift Witnesses 
We define `DriftWitness` as the data structure that records *where* this disagreement occurs.

Each constructor corresponds to a distinct kind of mismatch.

```agda
data DriftWitness (c s : Endpoint) : Set where
  MethodDrift :
    Endpoint.method c ≢ Endpoint.method s →
    DriftWitness c s

  MissingOnL :
    (st  : Status)
    (sc  : Schema)
    (lcN : lookup st (Endpoint.responses c) ≡ nothing)
    (lsJ : lookup st (Endpoint.responses s) ≡ just sc)
    → DriftWitness c s

  MissingOnR :
    (st  : Status)
    (sc  : Schema)
    (lcJ : lookup st (Endpoint.responses c) ≡ just sc)
    (lsN : lookup st (Endpoint.responses s) ≡ nothing)
    → DriftWitness c s

  MismatchAt :
    (st  : Status)
    (sc ss : Schema)
    (lcJ : lookup st (Endpoint.responses c) ≡ just sc)
    (lsJ : lookup st (Endpoint.responses s) ≡ just ss)
    (neq : sc ≢ ss)
    → DriftWitness c s
```
Interpretation:
- `MethodDrift` - Methods differ (e.g. `GET` vs `POST`)
- `MissingOnL`/`MissingOnR` - One side defines a response the other doesn't
- `MismatchAt` - Both define a response for the same status, but with different schemas

## Utils and lemmas
```agda
sym : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

nothing≠just : ∀ {A : Set} {x : A} → nothing ≢ just x
nothing≠just ()

just≠nothing : ∀ {A : Set} {x : A} → just x ≢ nothing
just≠nothing ()
```

## Drift Theorem
Any syntactic witness of drift guarantees that the two endpoints are not semantically compatible.

```agda
drift-theorem : ∀ {client server} → DriftWitness client server → ¬ Compatible client server
```

### Case 1: `MethodDrift`

Methods differ, but compatibility asserts equality.

```agda
drift-theorem {client} {server}
  (MethodDrift methods-not-equal)
  (methods-equal , _) =
  methods-not-equal methods-equal
```

### Case 2: `MissingOnL`

Server defines a response the client lacks.

```agda
drift-theorem {client} {server}
  (MissingOnL st sc lcN lsJ)
  (_ , allEq) =
  nothing≠just combined-equality
  where
    eq : lookup st (Endpoint.responses client)
       ≡ lookup st (Endpoint.responses server)
    eq = allEq st

    combined-equality : nothing ≡ just sc
    combined-equality = trans (sym lcN) (trans eq lsJ)
```

### Case 3: `MissingOnR`

Client defines a response the server lacks.

```agda
drift-theorem {client} {server}
  (MissingOnR st sc lcJ lsN)
  (_ , allEq) =
  just≠nothing combined-equality
  where
    eq : lookup st (Endpoint.responses client)
       ≡ lookup st (Endpoint.responses server)
    eq = allEq st

    combined-equality : just sc ≡ nothing
    combined-equality = trans (sym lcJ) (trans eq lsN)
```

### Case 4: `MismatchAt`

Client and server define the same status with different schemas.

```agda
drift-theorem {client} {server}
  (MismatchAt st sc ss lcJ lsJ neq)
  (_ , allEq) =
  neq (just-injective combined-equality)
  where
    eq : lookup st (Endpoint.responses client)
       ≡ lookup st (Endpoint.responses server)
    eq = allEq st

    combined-equality : just sc ≡ just ss
    combined-equality = trans (sym lcJ) (trans eq lsJ)
```

## Application

First we define some trivial lemmas we can use later

```agda
get-is-not-post : GET ≢ POST
get-is-not-post ()

todo-is-not-error : Todo ≢ Error
todo-is-not-error ()
```

### Example 1: MethodDrift

```agda
ClientGET : Endpoint
ClientGET = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Todo :: [])
  }

ServerPOST : Endpoint
ServerPOST = record
  { path = "/todos"
  ; method = POST
  ; body = HasBody Todo
  ; responses = (Case OK Todo :: [])
  }

methodDrift : DriftWitness ClientGET ServerPOST
methodDrift = MethodDrift get-is-not-post

methodDriftExample : ¬ Compatible ClientGET ServerPOST
methodDriftExample = drift-theorem methodDrift
```

### Example 2: MissingOnL

```agda
ClientMinimal : Endpoint
ClientMinimal = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Todo :: [])
  }

ServerExtended : Endpoint
ServerExtended = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Todo :: Case NotFound Error :: [])
  }

missingOnL : DriftWitness ClientMinimal ServerExtended
missingOnL = MissingOnL NotFound Error refl refl

missingOnLExample : ¬ Compatible ClientMinimal ServerExtended
missingOnLExample = drift-theorem missingOnL
```

### Example 3: MissingOnR

```agda
ClientExpecting404 : Endpoint
ClientExpecting404 = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Todo :: Case NotFound Error :: [])
  }

ServerSimpler : Endpoint
ServerSimpler = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Todo :: [])
  }

missingOnR : DriftWitness ClientExpecting404 ServerSimpler
missingOnR = MissingOnR NotFound Error refl refl

missingOnRExample : ¬ Compatible ClientExpecting404 ServerSimpler
missingOnRExample = drift-theorem missingOnR
```

### Example 4: MismatchAt


```agda
ClientOKTodo : Endpoint
ClientOKTodo  = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Todo :: [])
  }

ServerOKError : Endpoint
ServerOKError  = record
  { path = "/todos"
  ; method = GET
  ; body = NoBody
  ; responses = (Case OK Error :: [])
  }

mismatchAt : DriftWitness ClientOKTodo ServerOKError
mismatchAt = MismatchAt OK Todo Error refl refl todo-is-not-error

mismatchAtExample : ¬ Compatible ClientOKTodo ServerOKError
mismatchAtExample = drift-theorem mismatchAt
```

## Note

The current Drift Theorem establishes a baseline notion of compatibility for the REST DSL. It defines when two endpoints are *semantically identical*, i.e., they use the same HTTP method and produce exactly the same response schemas for all status codes. In practice, however, real-world drift often involves backward-compatible changes (e.g., adding optional fields, supporting extra status codes). These cases are not failures of equality but of **refinement**, where one version extends or relaxes another without breaking clients.

Future work will therefore aim to extend this theorem by replacing strict equality (≡) with a refinement relation on schemas and endpoints, allowing the system to formally distinguish between *breaking* and *safe* changes. The current result serves as the semantic backbone of the project - a verifiable base case for reasoning about API consistency and evolution.
