# Coq capabilities

Two patterns in one source file ([`Caps.v`](./Caps.v)) and one driver
([`driver.ml`](./driver.ml)). Run:

```
nix develop -c bash -c '../../generator/coq-build.sh Caps && node caps.js'
```

Expected output:

```
[vend]    counter Bump x3 → 1,2,3 ; Read = 3
  [host log] check 10
  [host log] check 20
  [host log] check 30
  [host log] check 40
[consume] validate (<100) [10,20,30,40] = true
  [host log] check 10
  [host log] check 20
  [host log] check 30
[consume] validate (<30)  [10,20,30,40] = false
```

## Consuming a host capability

```coq
Fixpoint validate (check : nat -> bool) (xs : list nat) : bool :=
  match xs with
  | []      => true
  | x :: xs' => andb (check x) (validate check xs')
  end.

Theorem validate_iff_forall : forall check xs,
  validate check xs = true <-> Forall (fun x => check x = true) xs.
```

The host's predicate enters as a normal Coq function value. After
extraction it's an OCaml `int -> bool` (because `ExtrOcamlNatInt` maps
`nat` to `int`); the OCaml driver supplies a logging wrapper:

```ocaml
let logged_pred upper x =
  Printf.printf "  [host log] check %d\n" x;
  x < upper
```

The verified `validate` walks the list and calls the wrapped predicate
on each element. Coq doesn't know about the side effect — that's
honest, because the logging happens at the OCaml seam, not in the
verified core.

**What's verified:** `validate_iff_forall` is the kind of specification
Coq is famous for: it says the boolean return value is *exactly* the
truth value of "every element satisfies `check`", expressed as a
`Forall` over a logical predicate. A caller can take the extracted
function, learn its iff-spec from the comment header, and trust it
without re-reading the implementation.

## Vending a capability via `Extract Constant`

Coq is pure; there's no way to express "a Counter object whose
internal state mutates" at the source level. The standard idiom is to
*declare* the interface as `Parameter`s and *bind* them to OCaml-side
implementations through `Extract Constant`:

```coq
Parameter Counter      : Type.
Parameter new_counter  : unit -> Counter.
Parameter bump         : Counter -> nat.
Parameter read         : Counter -> nat.

Extract Constant Counter      => "int ref".
Extract Constant new_counter  => "(fun () -> ref 0)".
Extract Constant bump         => "(fun r -> incr r; !r)".
Extract Constant read         => "(fun r -> !r)".
```

The first half is a Coq interface — type signatures the rest of the
proof script can use (including theorems that *reference* `bump` and
`read` opaquely). The second half is the OCaml realisation, only
visible to the extraction phase. The Coq side has nothing to prove
about the state because it never sees the state; this is honest about
where the trust boundary lives (the OCaml `ref` and its accessor
discipline).

OCaml-side use:

```ocaml
let c = Caps.new_counter () in
let a = Caps.bump c in   (* a = 1 *)
let b = Caps.bump c in   (* b = 2 *)
let r = Caps.read c in   (* r = 2 *)
```

After `js_of_ocaml`, all of this is wrapped into the same self-running
closure as the rest of the bundle. The host JS calls the OCaml-style
API (which means BigInts via the ExtrOcamlNatInt mapping), not a
JS-native one.

## Modularization story

Coq's modularization story is the multi-stage version of the same
friction we saw for Idris2 and Dafny, with extra steps:

1. **Two compilers in the toolchain.** Coq → OCaml → JS means a build
   step *per language* (`coqc`, `ocamlc`, `js_of_ocaml`). The repo's
   [`generator/coq-build.sh`](../../generator/coq-build.sh) glues them.
   The output is a single self-running .js, similar in shape to
   Idris2's `--cg node` output but with the js_of_ocaml runtime
   (~60 KB) inlined.

2. **No `module.exports`.** `js_of_ocaml` wraps everything in
   `(function (globalThis) { … }(globalThis));`. Reaching the verified
   `validate` from outside means either text-patching the bundle (like
   the Dafny path does) or using `js_of_ocaml`'s `Js.export` —
   demonstrated in the Endo / Agoric docs but not used here.

3. **Identifier mangling.** Inside the js_of_ocaml output, `validate`
   becomes a short alias like `bN`; the user's "I want to call sort
   from outside" workflow has to find it by structure, not name.

4. **OCaml 5 compatibility patch.** Coq 8.9's extraction emits
   `Pervasives.succ`; OCaml 5 renamed that to `Stdlib.succ`. The
   `coq-build.sh` does a one-shot `sed` to keep the pipeline working.

## What's verified vs not

The Coq type checker + tactic-discharged proofs guarantee:

- `validate` is total, deterministic, and satisfies its iff-spec
  against `Forall` (the `validate_iff_forall` theorem)
- The Counter *interface signatures* (`new_counter`, `bump`, `read`)
  are honored at every Coq call site

It does *not* guarantee:

- Anything about the OCaml-side Counter realisation. `Extract Constant
  bump => "(fun r -> incr r; !r)"` is OCaml code that Coq doesn't
  see. If the substituted body lied — say `(fun r -> 42)` — Coq would
  never know.
- Behaviour at the JS seam: js_of_ocaml's runtime decisions about
  exceptions, big-ints, and `TextDecoder` are below the verification
  layer.

This is the same seam pattern as the Agda capability port, just with
an extra compiler hop. The win over Agda is that Coq's tactic
language (`induction`, `inversion`, `nia`, `auto`) means the *proof*
side is shorter and more automated; the loss is that the extracted
output is ~3× larger than Idris2's and has no library surface at all.
