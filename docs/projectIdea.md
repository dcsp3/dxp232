# A Dependently Typed Domain-Specific Language for REST API Verification

**TLDR**

I want to build a small REST API system that proves itself correct using **dependent types**. Build a simple demo app: the goal is to show that the client and server literally cannot go out of sync (if they do, it just won’t compile)

---

### **The Problem**

Problems with REST API:

* A client might send the wrong kind of request  
* A server might return a response that doesn’t match what was promised  
* Compiles fine → crashes at runtime

Some “fixes” exist: 

* Swagger / OpenAPI  
* TypeScript, Zod, tRPC, io-ts, etc.  
* GraphQL

But they guarantee runtime-safety, not compile-time safety.

>Using a dependently typed approach, API specs can be encoded directly in the type system to ensure **compile-time proof** that the data structure aligns with its semantic content (e.g., status code, discriminant value)  

---

### **Motivation**

* Whole background \+ interest is basically web development (personal and professional)

* Experience at startups \+ big tech company and the issues they still run into  
  (e.g. HubSpot uses Zod which guarantees only runtime safety \- more on this later)

---

### **The Idea**

Dependent types allow us to formally define **invariants**, not just types:

"If status \= 200, the payload is Todo. If status \= 404, the payload is an Error message."

The goal is to build a fully functional, end-to-end **provably correct** system where the specification and implementation are always in-sync:

|   |   |
| :---- | :---- |
| **Agda Spec** | Formally defines the API and its invariants (the single, executable “source of truth”). |
| **Generated Server** | The code is structurally forced by the types to never construct an invalid status/payload combination (guaranteed valid responses). |
| **Generated Client** | The client's function signatures ensure it cannot possibly send a request that violates the server's contract (guaranteed valid requests). |
| **Demo App** | A small application that demonstrates zero-runtime contract errors (because all synchronisation is enforced at compile-time). |


>*Question: What are the logistics of translating Agda spec to server and client code (Haskell/TS)?*

---

### **Example \- Simple Todo API**

**Normal version (buggy)**

```python
# Server
app.get("/todos/:id", (req, res) => {
  # Bug: returns an error with 200 OK
  res.status(200).json({ error: "Todo not found" });
});

# Client
const todo = await api.getTodo(123);
console.log(todo.title);  # 💥 runtime crash
```

→ This compiles fine but crashes at runtime

**Dependently-typed version**

In Agda, I can say something like:

```agda
Response : Status → Set
Response 200 = Todo 
Response 400 = Error
```

→ If the server tries to send a `200` with an error, it won't compile  
→ If the client tries to access `todo.title` without checking the status, it also won't compile

---

### *Questions after the meeting*

* What is there to prove?  
* What are you solving? Why not just use TS?

Think about defining a language that captures interactions between client and server that can be:

* instantiated in Python/TS  
* formalised in agda

What properties will I have to prove about this language?

Other ideas to consider?

* Dependent types in python  
* C++ problems with variants