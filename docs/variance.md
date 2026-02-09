# Variance

Variance captures who consumes a value, and that determines the direction in which schema changes are safe. In our model:

- **Responses** are consumed by clients, so they are covariant 
- **Requests** are consumed by servers, so they are contravariant

When an API evolves, whether a change is safe depends on who observes the value:
- If clients consume a value (responses), safety means anything clients previously relied on must still be there.
- If servers consume a value (requests), safety means: the server must still accept everything it used to accept.

>These are opposite conditions, but they come from the same underlying idea: replaceability without breaking existing code.

---

## Why responses are covariant

For responses:
- Old schema = what clients expect
- New schema = what the server now produces

A change is safe if *the new response can be used wherever the old response was expected.*

So I define:

```
Schema⊑Co old new
```
to mean `new` is a safe replacement for `old` in client-observed positions.

---

## Why requests are contravariant

For requests:
- Old schema = what the server used to accept
- New schema = what the server accepts now

A change is safe if *every request that was valid before is still accepted.*

That reverses the direction of inclusion.

---

| Context | Data Flow | Who must stay tolerant? | Safe change | Forbidden change | Required-field rule |
|--------|----------|--------------------------|------------|----------------|--------------------|
| Responses (covariant) | Server → Client | Client | Add required/optional fields | Remove required fields | `oldReq ⊆ newReq` |
| Requests (contravariant) | Client → Server | Server | Remove required fields (accept more shapes) | Add required fields | `newReq ⊆ oldReq` |



