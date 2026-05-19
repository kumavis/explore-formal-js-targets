# jesc24 sealer pattern, in four languages

An exercise modelled on [`agoric-labs/jesc24`](https://github.com/agoric-labs/jesc24/blob/main/theories/heap_lang/lib/sealing.v):
a *dynamic sealer / unsealer* OCAP pattern, implemented in Dafny,
Agda, Idris2, and Coq. jesc24 itself verifies the pattern in Iris
separation logic over the HLA heap language; we don't reproduce that
proof — we exercise the same operational shape and compare what each
language's tooling can guarantee at the seam.

## The pattern

A *sealer* takes a value `v` and returns an opaque *token* `k`. The
matching *unsealer* takes a token `k` and returns:

- the originally sealed value, if `k` came from *this* sealer's `seal`
- nothing / aborts / `None`, if `k` came from *any other* sealer

The OCAP property is **token unforgeability**: a caller who only holds
references to other sealers' tokens cannot recover their values, even
if they pass them to `unseal`. The pattern is the standard
brand/key idiom.

```text
seal   : Sealer -> V -> Token
unseal : Sealer -> Token -> Maybe V       -- cross-sealer: Nothing
```

## Run all four

Inside `nix develop`:

```sh
# Dafny
( cd jesc24/dafny  && dafny build --target:js Sealer.dfy &&
                       NODE_PATH=$PWD/../../node_modules node Sealer.js )
# Agda
( cd jesc24/agda   && agda --js --js-optimize --compile-dir=. Sealer.agda &&
                       NODE_PATH=. node -e 'require("./jAgda.Sealer.js")' )
# Idris2
( cd jesc24/idris2 && rm -rf build && idris2 --cg node -o sealer Sealer.idr &&
                       node build/exec/sealer )
# Coq
( cd jesc24/coq    && ../../generator/coq-build.sh Sealer && node sealer.js )
```

Expected output (modulo formatting):

```text
s1.unseal(s1.seal(42))             = Just 42 / Some 42 / true / 42
s2.unseal(s1.seal(42))             = Nothing / None / verifier rejects
```

## How each language enforces unforgeability

| Language | Token identity mechanism | OCAP enforcement |
| --- | --- | --- |
| **Dafny**  | `class Box` — Dafny class references are unique per `new`. | **Compile-time.** `Unseal(b)` has precondition `b in tbl`; passing a Box from a different `Sealer` is a *verification error*. The cross-sealer call is commented in `Main` precisely because the verifier refuses it. |
| **Agda**   | A `postulate Token : Set` bound to a JS `Object.freeze({})` as a `WeakMap` key. | **Runtime, by lexical capture.** The JS-side `WeakMap` is private to the closure returned by `makeSealer`; only that closure can `.has()` / `.get()`. Cross-sealer `unseal` returns the `nothing` constructor. |
| **Idris2** | An ADT `data Token = MkToken Nat` (constructor only visible in this module) plus a per-sealer counter. | **Imperfect.** Within-sealer round-trip is verified by Idris2's type checker; cross-sealer is correctly `Nothing` *if* the second sealer hasn't issued a token with the same internal Nat. The demo deliberately triggers and labels the collision case. A real OCAP implementation here would use FFI to a JS `WeakMap`, like Agda. |
| **Coq**    | `Parameter Token : Type.` bound to OCaml `unit ref`; the `unseal` body uses physical equality (`==`). | **Runtime, by OCaml ref identity.** OCaml's `ref ()` is unforgeable at the ABI level (allocates a fresh box); physical equality `==` is the discrimination primitive. The Coq side cannot *prove* this — `Extract Constant` is opaque to the proof checker — but the typed interface (`Sealer -> Token -> option nat`) is enforced at every Coq call site. |

## What we can claim about each

**Dafny is the only one with a compile-time-checked OCAP guarantee**
on the unseal side: `requires b in tbl` propagates as a proof
obligation to every caller. A reviewer reading `Sealer.dfy` knows
that any well-typed program is incapable of unsealing a foreign token
— the verifier rules it out before code generation.

**Agda gets the strongest *operational* guarantee** through a JS
`WeakMap` keyed by frozen objects. The privacy is a property of the JS
runtime (lexical closure + WeakMap), not Agda's logic; but the
runtime side is exactly the same primitive every other JS OCAP
implementation uses.

**Idris2's pure-Idris implementation can't enforce unforgeability**
without FFI — the int-based token encoding has collisions across
sealers. The demo shows this honestly:
`s2.unseal(s1.seal(42)) = Nothing` initially, but after `s2.seal(99)`
the same s1-issued token suddenly unseals to `Just 99`. The fix is
the Agda approach (FFI to a JS WeakMap), at which point the Idris2
implementation has the same operational guarantee as Agda.

**Coq inherits OCaml's `==` semantics.** OCaml's physical equality on
heap-allocated refs is rock-solid; the Coq side just types the
interface and trusts the realisation. The honest framing is "the
trust boundary is the `Extract Constant` line."

## Differences from jesc24

We don't reproduce the Iris separation-logic proof — that lives in
hundreds of lines of `iProp Σ`, persistent / non-persistent
predicates, and ghost state. What we ARE doing is matching the
*operational shape* (`make_seal` returning a pair of closures) and
comparing how much of the OCAP guarantee each language's tooling
delivers without separation logic.

If you wanted to lift one of these to a jesc24-style proof, the Coq
port is the natural starting point: drop the `Extract Constant`
bodies, replace `Parameter` with full HLA definitions, and reuse the
Iris triples for `is_seal` / `is_unseal` / `is_sealed`. The path from
"runnable demo" to "verified pattern" is straightforward — it's the
same Coq file, just with the implementation moved from OCaml to HLA.
