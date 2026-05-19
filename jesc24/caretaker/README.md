# jesc24 caretaker, in four languages

A *caretaker* wraps an underlying target function `f` and exposes a
revocable `wrap` operation. `enable` / `disable` toggle a private
flag; while disabled, `wrap` refuses. This is the canonical OCAP
revocation primitive — a holder of the caretaker can pass `wrap` to
an untrusted party, then `disable` to revoke all future access
without ever sharing the underlying `f` directly.

The shape mirrors
[`agoric-labs/jesc24/theories/heap_lang/lib/caretaker.v`](https://github.com/agoric-labs/jesc24/blob/main/theories/heap_lang/lib/caretaker.v):

```text
make_caretaker : (Nat -> Nat) -> IO Caretaker
wrap           : Caretaker -> Nat -> IO (Maybe Nat)   -- Nothing when disabled
enable         : Caretaker -> IO ()
disable        : Caretaker -> IO ()
```

(jesc24's `wrap` `abort`s when disabled; we return `Nothing` so the
demo can `print` the revoked case rather than crash.)

## Run all four

Inside `nix develop`:

```sh
# Dafny
( cd jesc24/caretaker/dafny  && dafny build --target:js Caretaker.dfy &&
                                 NODE_PATH=$PWD/../../../node_modules node Caretaker.js )
# Agda
( cd jesc24/caretaker/agda   && agda --js --js-optimize --compile-dir=. Caretaker.agda &&
                                 NODE_PATH=. node -e 'require("./jAgda.Caretaker.js")' )
# Idris2
( cd jesc24/caretaker/idris2 && rm -rf build && idris2 --cg node -o caretaker Caretaker.idr &&
                                 node build/exec/caretaker )
# Coq
( cd jesc24/caretaker/coq    && ../../../generator/coq-build.sh Caretaker && node caretaker.js )
```

Expected output (identical across all four, modulo `Just`/`Some`/`just`):

```text
default (disabled): wrap 10 = nothing
enabled:            wrap 10 = just 20
enabled:            wrap 7  = just 14
disabled:           wrap 10 = nothing
```

## How each language enforces revocation

| Language | Where the flag lives | Revocation enforcement |
| --- | --- | --- |
| **Dafny**  | `var enabled : bool` on the `Caretaker` class. | **Two-level.** A `Wrap` method has `requires enabled`, so callers who can't prove the caretaker is currently enabled *cannot type-check the call at all*. `TryWrap` returns `(ok, r)` and runtime-checks the flag — used here so the demo can show both states. |
| **Agda**   | A JS `let on = false` captured in the closure returned by `makeCaretaker`. | **Runtime, by lexical capture.** The flag is unreachable from outside the closure; `wrap` / `enable` / `disable` are the only accessors. |
| **Idris2** | An `IORef Bool` captured in the closure returned by `makeCaretaker`. | **Runtime, by IORef privacy.** The `IORef` is `let`-bound inside the IO action; only the three closures returned ever reach it. |
| **Coq**    | An OCaml `bool ref` inside the record-typed `Caretaker`, bound through `Extract Constant`. | **Runtime, by OCaml field privacy.** Coq types the interface; OCaml realises the mutable cell. The Coq side could prove a state machine over `enabled` if we replaced `Parameter`+`Extract` with HLA code, but here it's pure FFI. |

## What we can claim about each

**Dafny is the only one with a compile-time revocation guarantee.**
A caller in possession of the caretaker reference plus the `requires
enabled` discipline *cannot call `Wrap` from a context where the
verifier hasn't established the flag is true*. For untrusted callers
this is what you want: they call `TryWrap` (or rely on `wrap`-with-
runtime-check), and the strict path is unavailable without a proof.

**Agda, Idris2, and Coq all rely on the host language's existing
state-privacy primitive** (JS closure, IORef, OCaml `mutable
record`). The guarantee is operational, not formal — exactly the
same trust model SES gives you in vanilla JS. The Coq version could
be lifted to a formal proof by porting the OCaml realisation into Coq
itself (essentially what jesc24 does in HLA, just without the Iris
separation logic on top).

## Differences from jesc24

jesc24's `caretaker.v` defines TWO variants: a *blocking* caretaker
(`wrap` waits for a lock when contended) and a *non-blocking*
caretaker (`wrap` aborts immediately if disabled). Our four ports are
the non-blocking variant; the blocking version requires a mutex
primitive (`lock.v`) which we don't model.

The full Iris specification ties `enabled γ true` / `enabled γ false`
to ghost state and proves the protocol via persistence + framing.
We sidestep all of that and just verify operational correctness
(Dafny) or rely on the host's state-privacy (the other three).
