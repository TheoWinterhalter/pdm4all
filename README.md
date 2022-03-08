# Partial Dijkstra monads for all

Construction of partial Dijkstra monads using the Dijkstra monads for all
construction.

Should work fine with Coq 8.14. Just build with `make`.

## Motivation: Examples of partiality in F*

These should type-check from the existence of a lift from PURE.
They explain the need for deep asserts in the effect representation.

State:
```fstar
let s₀ = get () in
let s₁ = get () in
assert (s₀ = s₁)
```

ND:
```fstar
let x = choose l in
assert (x `memP` l)
```