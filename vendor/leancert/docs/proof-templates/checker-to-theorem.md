# Checker-To-Theorem Pattern

Most LeanCert certificate APIs follow the same trust pattern:

```text
computable checker = true
+ soundness theorem
= semantic theorem
```

The checker may run through `decide`, `native_decide`, or a tactic-generated
proof term.  The trusted part is not the search process; it is the theorem that
interprets a successful checker result.

This pattern is described architecturally in:

- [Golden Theorems](../architecture/golden-theorems.md)
- [Verification Status](../architecture/verification-status.md)

Use this page as the conceptual bridge between direct automation and structured
certificate templates.
