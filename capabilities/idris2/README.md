# Idris2 capabilities

Two patterns in one source file ([`Caps.idr`](./Caps.idr)) and one driver
([`driver.mjs`](./driver.mjs)). Run:

```
nix shell nixpkgs#idris2 --command idris2 --cg node -o caps Caps.idr
node driver.mjs
```

Expected output:

```
[vend]    counter Bump x3 → 1,2,3 ; Read = 3
  [host log] 10
  [host log] 20
  [host log] 30
  [host log] 40
  [host log] 10
  [host log] 20
  [host log] 30
[consume] validate (<100) [10,20,30,40] = True
[consume] validate (<30)  [10,20,30,40] = False
```

## Consuming a host capability

Idris2's `%foreign` is the cleanest inline FFI of the three tools. The
host installs a function on `globalThis` and Idris2 reaches it by name:

```idris
%foreign "javascript:lambda: (x) => globalThis.__hostLog(Number(x))"
prim__hostLog : Int -> PrimIO ()

hostLog : Int -> IO ()
hostLog n = primIO (prim__hostLog n)

validate : (Int -> Bool) -> List Int -> IO Bool
validate _ []       = pure True
validate p (x :: xs) = do
  hostLog x
  if p x then validate p xs else pure False
```

The pragma string says "this Idris2 declaration is implemented by *this
JS lambda*". The type guarantees the host gets an `Int` and gets back
nothing-of-interest (`PrimIO ()`), which `primIO` lifts into `IO ()`.

The predicate `p : Int -> Bool` is a normal Idris2 function and is
*already* in scope — no FFI needed for it. The driver just passes
Idris2 lambdas (`\x => x < 100`).

To make the host's predicate available the same way as the log, replace
the lambda with `prim__hostPred` of the same shape — `%foreign` accepts
any JS expression that returns the right thing.

## Vending a capability

Idris2 has `Data.IORef`, so the counter is a four-line builder:

```idris
record Counter where
  constructor MkCounter
  bump : IO Nat
  read : IO Nat

makeCounter : IO Counter
makeCounter = do
  ref <- newIORef Z
  pure $ MkCounter
    (do v <- readIORef ref
        let v' = S v
        writeIORef ref v'
        pure v')
    (readIORef ref)
```

The `IORef` is private to the `do`-block — it never appears in the
record. The host has no path to it except through the closed-over
`bump` / `read` thunks. That's the same object-capability discipline
SES leans on, encoded at the language level.

What Idris2 *can't* check here is the closed-form invariant
"`count` equals the number of `bump` calls". `bump` lives in `IO`, so
Idris2 sees its return type but not its effect on the ref. To prove
that you'd need either a more refined `IORef` abstraction with a
ghost-state index, or to shift to a state-monad encoding and prove
properties there.

## Modularization story

Idris2's `--cg node` produces an executable, not a module:

```js
#!/usr/bin/env node
class IdrisError extends Error { }
function __prim_js2idris_array(x){ ... }
…
function Main_makeCounter() { … }
…
const __mainExpression_0 = Main_main(null);
try { __mainExpression_0() } catch (e) { … }
```

Three observations:

1. **Self-contained, but a script.** No `require()` of external
   modules — the whole runtime (`__prim_js2idris_array`, `__lazy`,
   `__tailRec`, …) is inline. Great for the SES Compartment story
   (`Compartment.evaluate(source)` works as-is), terrible for
   "import this as a library and call `makeCounter` from elsewhere".

2. **`module.exports` is missing.** The driver here side-steps the
   problem by installing the host capability on `globalThis` *first*
   and then `eval`-ing the file — `main` runs and reaches out to the
   global. For the *vend* direction we don't actually let the host
   hold the counter; we use it from inside Idris2's `main`. To export
   it cleanly we'd need either the bundle preprocessing trick (see
   `generator/bundle.mjs` in the repo root) or for Idris2 to grow a
   `%export "javascript:identifier" foo` story.

3. **Per-element host calls are expensive.** Every `hostLog x` is a
   `%foreign` call through `primIO`. If the host capability is
   chatty, batching at the Idris2 side or buffering on the JS side is
   the optimization.

## What's verified vs not

The Idris2 type checker guarantees:

- `validate` walks the whole list when the predicate is monotone-true
  (no element is silently skipped)
- The counter record's constructor is the only way to build one — the
  IORef is genuinely private
- Both functions are total (we declared `%default total` in spirit; see
  also the [`sum-formula` writeup](../../EVALUATION.md))

It does *not* guarantee:

- That `bump` always returns "previous-read + 1" (an effectful invariant)
- That the host's `__hostLog` does anything useful (it could be a no-op
  or a misbehaving spy — Idris2 only sees its type)

A bundle-source bundle of this code imports cleanly into a SES
Compartment with just `{ console }` endowed — see the SES matrix in
`docs/insertion-sort.md` for that data.
