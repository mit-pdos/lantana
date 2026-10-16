# Lantana in Lean

A Lean 4 reimplementation of *Lantana*, a concurrent separation logic for liveness
("Decoupling Liveness Obligations from Threads in the Lantana Concurrent Separation Logic",
POPL 2027), on top of Transfinite Iris-Lean.

- Lean `v4.34.1`; depends on the `Iris/` package of
  [dongjaelee1/iris-lean](https://github.com/dongjaelee1/iris-lean), branch `transfinite`
  (step index `Iris.SI := Ordinal.{3}`), and through it on its `Ordinals` package.
- Reference: the Rocq development of Lantana (`dev`, commit `0c1515a`). Lean declarations
  carry `@[lantana_alias rocqName]`; deliberate omissions are `#lantana_ignore`d.

## Build

```
lake build            # the library
lake test             # LantanaTest
scripts/audit.sh      # no sorry / admit / axiom / native_decide
```

## Layout

`Lantana/Prelude`, `Algebra`, `BaseLogic`, `ProgramLogic`, `Trace`, `HeapLang`, `Examples`
(see the module docstrings); `LantanaTest/` holds the tests.
