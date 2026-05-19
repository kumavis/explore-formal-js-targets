# Agda capabilities

Two patterns in one source file ([`Caps.agda`](./Caps.agda)) and one driver
([`driver.mjs`](./driver.mjs)). Run:

```
nix develop -c bash -c 'agda --js --js-optimize --compile-dir=. Caps.agda && node driver.mjs'
```

Expected output:

```
[vend]    counter Bump x3 → 1,2,3 ; Read = 3
  [host log] 10
  [host log] 20
  [host log] 30
  [host log] 40
[consume] validate (<100) [10,20,30,40] = true
  [host log] 10
  [host log] 20
  [host log] 30
[consume] validate (<30)  [10,20,30,40] = false
```

## Wiring IO at all

Agda is a proof assistant first; `Agda.Builtin.IO` declares only the
*type* `IO : Set -> Set` and nothing else. There's no built-in `return`
or `bind`, so any program that does IO has to wire its own. We did that
with two `postulate`s and inline `{-# COMPILE JS #-}` definitions:

```agda
postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B
{-# COMPILE JS return = (_) => (x) => (cb) => cb(x) #-}
{-# COMPILE JS _>>=_  = (_) => (_) => (m) => (k) => (cb) => m((v) => k(v)(cb)) #-}
```

This bind has a CPS-shaped JS encoding because Agda's IO at the
`--js` backend uses continuation-passing — the `(cb) => …` is the
continuation each action calls with its result. Get the encoding
wrong and your program type-checks but hangs at runtime.

Agda *does* have a built-in `do`-notation that desugars to `_>>=_`
once you declare a `_>>=_` operator in scope, so the demo's `do`-free
body is a stylistic choice, not a limitation. We used explicit `>>=`
+ lambdas to make the continuation chain visible.

## Consuming a host capability

The host capability is just another postulate with a JS body:

```agda
postulate
  hostLog : Nat -> IO ⊤
{-# COMPILE JS hostLog = (n) => (cb) => { globalThis.__hostLog(Number(n)); cb({}); } #-}
```

…and the validator is plain Agda over `(Nat -> Bool)` and `List Nat`:

```agda
validate : (Nat -> Bool) -> List Nat -> IO Bool
validate _ []       = return true
validate p (x ∷ xs) = hostLog x >>= \_ -> aux (p x)
  where
    aux : Bool -> IO Bool
    aux true  = validate p xs
    aux false = return false
```

(`if_then_else_` lives in stdlib `Data.Bool`, not in
`Agda.Builtin.Bool`, so pattern-matching is more frugal than an import.)

The host's `Nat -> Bool` predicate enters as a regular function value —
Agda's curried JS encoding (`f(null)(x)` because of erased type
parameters) means a JS-side function works if you wrap it. In the demo
we use Agda-side lambdas (`\x -> x < 100`) and let Agda compile them
directly.

## Vending a capability

Agda has no mutable state at the language level. The counter is
therefore another `{-# COMPILE JS #-}` postulate where the JS side
does the actual closing-over-a-cell:

```agda
postulate
  Counter     : Set
  makeCounter : IO Counter
  bumpC       : Counter -> IO Nat
  readC       : Counter -> IO Nat
{-# COMPILE JS Counter     = null #-}
{-# COMPILE JS makeCounter = (cb) => { let n = 0n; cb({ bump: () => ++n, read: () => n }); } #-}
{-# COMPILE JS bumpC       = (c) => (cb) => cb(c.bump()) #-}
{-# COMPILE JS readC       = (c) => (cb) => cb(c.read()) #-}
```

To the Agda code, `Counter` is an opaque `Set`; the only operations are
the typed `bumpC` / `readC` calls. To JS, the value is a plain object
with two methods that share a private cell.

This shape — *the JS object IS the capability, Agda just types it* — is
honest: Agda's logic doesn't reach inside the closure, and pretending
otherwise would be a verification lie. If you want Agda to prove
"`bump` always returns `previous-read + 1`", you have to encode the
state symbolically (state monad / indexed types) instead of going
through this FFI.

## Modularization story

Agda's `--js` backend is the strongest of the three for the
"library you can `require()`" case:

1. **Every top-level definition is on `module.exports`.** The driver
   does `require('./jAgda.Caps.js')` and `main` runs as a side effect
   (and the other exports — `validate`, `makeCounter`, `bumpC`,
   `readC` — are reachable directly).

2. **Multi-file output.** Agda emits one `jAgda.<Module>.js` per Agda
   module, plus `agda-rts.js`. The driver sets `NODE_PATH` to the
   emit directory so the sibling `require()`s resolve. The repo's
   `generator/bundle.mjs` shows how to fold the whole tree into a
   single `@endo/bundle-source` bundle for SES Compartment use.

3. **Curried JS calling convention.** Calls from JS look like
   `mod.validate(null)(pred)(xs)(callback)` because Agda's emitter
   threads `null` for each erased type parameter and CPSes IO. The
   demo hides this behind the `do`-style chain on the Agda side, but
   when you write the JS host you'll feel it.

## What's verified vs not

The Agda type checker guarantees:

- The validator visits every element before short-circuiting (the
  `hostLog x >>= \_ -> aux (p x)` order can't be swapped)
- The IO bind's CPS contract is honored at every call site (it's
  type-checked, even if the JS body is unchecked)
- Pattern coverage on `Bool` and `List Nat` is exhaustive

It does *not* guarantee:

- Anything about the JS side of the postulates — `bumpC`'s JS body
  could return `42n` every time and Agda wouldn't notice
- That the `Counter` object's `bump` / `read` actually share a cell
  (Agda only sees the typed surface)

In other words: Agda's verification is strongest on the *pure logic*
side and stops at the FFI seam. For capabilities that genuinely need
mutation, the proof lives in the JS reviewer's head, not in Agda.
