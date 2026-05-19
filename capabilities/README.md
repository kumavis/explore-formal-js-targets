# Capabilities: passing them in, vending them out

A separate exploration from the main 5-problem comparison. For each
tool we built two small examples:

1. **Consuming a capability** — the verified program receives a
   host-supplied function it can call (a predicate, a logger), and uses
   it inside its own typed logic.

2. **Vending a capability** — the verified program produces an opaque
   object the host holds and operates through (a counter with `Bump` /
   `Read`).

Each language gets a self-contained source + driver + writeup; the
approaches differ because each language's idiom and FFI affordances
differ. None of these wire into the main `generator/` pipeline.

| Language | Writeup | Highlight |
| --- | --- | --- |
| Dafny  | [`dafny/README.md`](./dafny/README.md)   | Verified `class Counter` whose `Bump` / `Read` postconditions are SMT-checked. The class compiles to a real JS class. |
| Agda   | [`agda/README.md`](./agda/README.md)     | Pure language, so all state crosses the seam through `postulate + COMPILE JS`. Best library surface of the four after a sibling-require fix-up. |
| Idris2 | [`idris2/README.md`](./idris2/README.md) | `IORef`-backed counter inside a record — closest in feel to ordinary hand-written JS. `%foreign` is the cleanest inline FFI. |
| Coq    | [`coq/README.md`](./coq/README.md)       | `Parameter` + `Extract Constant` binds a Coq-side interface to an OCaml-implemented `int ref`. The validator gets a real `iff` proof (`validate_iff_forall`) — the strongest spec of the four. |

## Quick read

If you only have time for one, **[Idris2](./idris2/README.md)** is the
most immediately useful: the code looks like idiomatic functional JS,
`%foreign` is one line per host call, and the bundled compartment story
(see the main `EVALUATION.md`) is the smoothest.

**[Dafny](./dafny/README.md)** is the most *interesting* if you care
about verified invariants on the vended capability — it's the only
tool of the four that proves "every `Bump` increases `count` by
exactly 1" at compile time.

**[Coq](./coq/README.md)** has the strongest *specification* of the
consumed predicate (a real `iff` against a `Forall`), at the cost of
the multi-stage extraction pipeline and the largest bundle.

**[Agda](./agda/README.md)** is the most honest about the seam — it
acknowledges that verification stops at the FFI boundary, and that any
"mutation" claim about the JS object lives in the reviewer's head.
