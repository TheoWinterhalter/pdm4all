# Partial Dijkstra monads for all

Construction of partial Dijkstra monads using the Dijkstra monads for all
construction.

## Requirements and build

Should work fine with Coq 8.14 and Equations 1.3.

Just build with `make`.

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

## Description of the files

The Coq development is all in `theories`.

### General construction

- `structures.v` contains definitions of monads, Dijkstra monads, monad
transformers…
- `guarded.v` describes the partiality monad.
- `PURE.v` proposes a simple encoding of F*'s `PURE` effect.
- `PDM.v` contains the general partial Dijkstra monad construction.

### Special cases

- `GuardedPDM.v` proposes a construction of partial DM from a monad without
asserts.
- `DM4Free.v` makes the Dijkstra monads for free work fit in the current
framework.
- `FreePDM.v`: get a partial Dijkstra monad from a free monad signature and
a specification monad.

### Examples

- `StateSpec.v`: Specification monad for state.
- `State.v`: State using the state monad (equivalent to `DM4FreeState.v`)
- `StateFree.v`: State defined with a free monad.
- `DM4FreeState.v`: State using DM4Free construction.
- `ND.v`: Non-determinism.
- `Div.v`: Non-termination.

## F* examples

They are found in the `fstar` directory and tested with
```
F* 2021.11.05~dev
commit=d20e32ca8ef7ab2e4cc79e0f553687ee2ae4a2ed
```

- `ND.fst`: Non-determinism.