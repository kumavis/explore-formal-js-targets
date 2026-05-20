# Factorial (with positivity proof)

Recursive factorial function with a proof that the result is at least 1. Dafny uses an SMT-discharged postcondition; Agda and Idris2 use an inductive predicate inhabited by a constructive term.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 31 | 584 | 1,499 + 30,838 = 32,337 | `factorial(5) = 120` | ✅ ok |
| Agda | 40 | 1,343 | 1,565 + 14,926 = 16,491 | `120` | ✅ ok |
| Idris2 | 22 | 619 | 403 + 9,818 = 10,221 | `120` | ✅ ok |
| Coq | 26 | 581 | 1,624 + 68,794 = 70,418 | `factorial(5) = 120` | ✅ ok |

## SES compatibility

| Language | Needs bundling | Static scan | `lockdown()` + `require()` | Raw `Compartment.evaluate()` | Bundled (`@endo/bundle-source` → `importBundle`) | Compartment endowments |
| --- | :---: | :---: | :---: | :---: | :---: | --- |
| Dafny | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass | `console` + `BigNumber` + `Math` |
| Agda | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass | `console` |
| Idris2 | no | ✅ clean | ✅ pass | ✅ pass | ✅ pass | `console` |
| Coq | no | ✅ clean | ✅ pass | ❌ evaluate-failed | ❌ import-failed | `console` + `TextDecoder` + `TextEncoder` + `Int8Array` + `Uint8Array` + `Uint8ClampedArray` + `Int16Array` + `Uint16Array` + `Int32Array` + `Uint32Array` + `Float32Array` + `Float64Array` + `BigInt64Array` + `BigUint64Array` + `ArrayBuffer` + `DataView` |

> **Dafny bundling requirement:** the bundled compartment passes only with `Math` (in addition to `BigNumber`) endowed. Dafny's emitted runtime calls `bignumber.js`, which invokes `Math.random()` during initialization — SES's secure-mode `Math` removes `random`, so without the endowment the bundle imports fail at load. A real deployment should wrap `Math` rather than passing the host's.

> **Coq bundling requirement:** js_of_ocaml's runtime reaches for `TextDecoder`/`TextEncoder` and the full set of typed-array constructors (`Float32Array`, `Int32Array`, `ArrayBuffer`, `DataView`, …); SES Compartments don't expose those by default, so they must be endowed. Even with those endowed, the bundle still fails import — see the Coq footnote below.

> **Coq Compartment failure (importBundle path):** js_of_ocaml's runtime writes a `jsoo_create_file` helper onto `globalThis` during init. `@endo/import-bundle` creates its Compartment with a **non-extensible globalThis**, so the assignment throws `Cannot add property …, object is not extensible`. This is *not* a fundamental SES restriction — a hand-rolled `new Compartment(endowments).evaluate(source)` *does* allow the assignment (its globalThis is extensible), and the Coq bundle runs end-to-end there with the same endowments. The blocker is therefore `@endo/import-bundle`'s policy, not `lockdown()` itself.

> **Coq raw `Compartment.evaluate()` failure (default endowments):** the runtime asks for `TextDecoder` before anything else and the default Compartment doesn't expose it. This is a Compartment-globals omission (same shape as Dafny needing `Math` endowed), fixed by including the constructors listed in the Compartment-endowments column.

### Bundle details

| Language | Bundle bytes (base64) | Imported keys | Notes |
| --- | ---: | --- | --- |
| Dafny | 162,956 | _dafny, _System, Factorial, _module, default | imported keys: _dafny, _System, Factorial, _module, default |
| Agda | 37,948 | IsPositive, factorial, natToString, putStrLn, main, default, mul-pos, factorial-pos | imported keys: IsPositive, factorial, natToString, putStrLn, main, default, mul-pos, factorial-pos |
| Idris2 | 15,380 | factorial, default | imported keys: factorial, default |
| Coq | 98,976 | — | import error: `Cannot add property jsoo_create_file, object is not extensible` |

---

## Dafny

**Source** (`problems/factorial/dafny/Factorial.dfy`):

```dafny
// Factorial with a postcondition that the result is always positive.
// Dafny discharges the proof with its SMT backend; no manual lemma needed.

module Factorial {

  function Fact(n: nat): nat
    ensures Fact(n) >= 1
  {
    if n == 0 then 1 else n * Fact(n - 1)
  }

  method Compute(n: nat) returns (r: nat)
    ensures r == Fact(n)
  {
    r := 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant r == Fact(i)
    {
      i := i + 1;
      r := r * i;
    }
  }

  method Main() {
    var r := Compute(5);
    print "factorial(5) = ", r, "\n";
  }
}

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `factorial(5) = 120`

**Generated JS — user code only** (from `Factorial.js`, 32,337 bytes total, 1,499 shown; runtime prelude elided):

```js
let Factorial = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Factorial._default";
    }
    _parentTraits() {
      return [];
    }
    static Fact(n) {
      let _0___accumulator = _dafny.ONE;
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ONE).multipliedBy(_0___accumulator);
        } else {
          _0___accumulator = (_0___accumulator).multipliedBy(n);
          let _in0 = (n).minus(_dafny.ONE);
          n = _in0;
          continue TAIL_CALL_START;
        }
      }
    };
    static Compute(n) {
      let r = _dafny.ZERO;
      r = _dafny.ONE;
      let _0_i;
      _0_i = _dafny.ZERO;
      while ((_0_i).isLessThan(n)) {
        _0_i = (_0_i).plus(_dafny.ONE);
        r = (r).multipliedBy(_0_i);
      }
      return r;
    }
    static Main(__noArgsParameter) {
      let _0_r;
      let _out0;
      _out0 = Factorial.__default.Compute(new BigNumber(5));
      _0_r = _out0;
      process.stdout.write((_dafny.Seq.UnicodeFromString("factorial(5) = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(_0_r));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
  };
  return $module;
})(); // end of module Factorial

// ... runtime prelude elided ...

_dafny.HandleHaltExceptions(() => Factorial.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
```

---

## Agda

**Source** (`problems/factorial/agda/Factorial.agda`):

```agda
-- Factorial with a proof that the result is always at least 1.
-- The proof is a separate term inhabiting a propositional type.

module Factorial where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- The function itself.
factorial : Nat -> Nat
factorial zero    = 1
factorial (suc n) = (suc n) * factorial n

-- Witness that a Nat is a successor (i.e. >= 1).
data IsPositive : Nat -> Set where
  pos : (n : Nat) -> IsPositive (suc n)

-- Lemma: the product of two positives is positive.
mul-pos : (a b : Nat) -> IsPositive a -> IsPositive b -> IsPositive (a * b)
mul-pos (suc a) (suc b) (pos _) (pos _) = pos _

-- The theorem: factorial n is always positive.
factorial-pos : (n : Nat) -> IsPositive (factorial n)
factorial-pos zero    = pos 0
factorial-pos (suc n) = mul-pos (suc n) (factorial n) (pos n) (factorial-pos n)

-- An executable entry point printing factorial 5.
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate
  natToString : Nat -> String
  putStrLn    : String -> IO ⊤
{-# COMPILE JS natToString = function (n) { return n.toString(); } #-}
{-# COMPILE JS putStrLn    = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (natToString (factorial 5))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `120`

*(`agda-rts.js`, 10,831 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Bool.js`, 187 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Char.js`, 743 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Equality.js`, 167 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.IO.js`, 126 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.List.js`, 250 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Maybe.js`, 224 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Nat.js`, 500 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Sigma.js`, 295 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.String.js`, 1,281 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Unit.js`, 139 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Primitive.js`, 155 bytes — runtime / stdlib, elided)*

**Generated JS — user code only** (from `jAgda.Factorial.js`, 1,593 bytes total, 1,565 shown; runtime prelude elided):

```js
var agdaRTS = require("agda-rts");

var z_jAgda_Agda_Builtin_Equality = require("jAgda.Agda.Builtin.Equality");
var z_jAgda_Agda_Builtin_IO = require("jAgda.Agda.Builtin.IO");
var z_jAgda_Agda_Builtin_Nat = require("jAgda.Agda.Builtin.Nat");
var z_jAgda_Agda_Builtin_String = require("jAgda.Agda.Builtin.String");
var z_jAgda_Agda_Builtin_Unit = require("jAgda.Agda.Builtin.Unit");
var z_jAgda_Agda_Primitive = require("jAgda.Agda.Primitive");

exports["IsPositive"] = {};
exports["factorial"] = a => agdaRTS.uprimIntegerEqual(agdaRTS.primIntegerFromString("0"),a)? agdaRTS.primIntegerFromString("1"): (
    b => agdaRTS.uprimIntegerMultiply(a,exports["factorial"](b()))
  )(
    () => agdaRTS.uprimIntegerMinus(a,agdaRTS.primIntegerFromString("1"))
  );
exports["IsPositive"]["pos"] = a => b => b["pos"](a);
exports["mul-pos"] = a => b => c => d => agdaRTS.primSeq(
    c,
    agdaRTS.primSeq(d,exports["IsPositive"]["pos"](null))
  );
exports["factorial-pos"] = a => agdaRTS.uprimIntegerEqual(agdaRTS.primIntegerFromString("0"),a)? exports["IsPositive"]["pos"](null): (
    b => exports["mul-pos"](null)(null)(exports["IsPositive"]["pos"](null))(exports["factorial-pos"](b()))
  )(
    () => agdaRTS.uprimIntegerMinus(a,agdaRTS.primIntegerFromString("1"))
  );
exports["natToString"] = function (n) { return n.toString(); };
exports["putStrLn"] = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; };
exports["main"] = exports["putStrLn"](
    exports["natToString"](
      exports["factorial"](agdaRTS.primIntegerFromString("5"))
) );
```

---

## Idris2

**Source** (`problems/factorial/idris2/Factorial.idr`):

```idris
||| Factorial with a proof that the result is always a successor (>= 1).
||| The proof is a dependently-typed term that Idris2 checks at compile time.

module Factorial

%default total

factorial : Nat -> Nat
factorial Z     = 1
factorial (S n) = (S n) * factorial n

-- Theorem: factorial n is always a successor.
-- Returned as a dependent pair (k ** factorial n = S k).
factorialPos : (n : Nat) -> (k : Nat ** factorial n = S k)
factorialPos Z     = (Z ** Refl)
factorialPos (S n) =
  case factorialPos n of
    (k ** prf) => ((k + n * S k) ** rewrite prf in Refl)

main : IO ()
main = putStrLn (show (factorial 5))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `120`

**Generated JS — user code only** (from `factorial`, 10,221 bytes total, 403 shown; runtime prelude elided):

```js
function Factorial_main($0) {
 return Prelude_IO_prim__putStr((Prelude_Show_show_Show_Nat(Factorial_factorial(5n))+'\n'), $0);
}

function Factorial_factorial($0) {
 switch($0) {
  case 0n: return 1n;
  default: {
   const $2 = ($0-1n);
   return (($2+1n)*Factorial_factorial($2));
  }
 }
}
try{__mainExpression_0()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }
```

---

## Coq

**Source** (`problems/factorial/coq/Factorial.v`):

```coq
(* Factorial in Coq, with extraction to OCaml. *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

Lemma fact_pos : forall n, 1 <= fact n.
Proof.
  induction n; simpl.
  - apply Nat.le_refl.
  - destruct (fact n) eqn:E.
    + inversion IHn.
    + apply le_n_S, Nat.le_0_l.
Qed.

Extraction Language OCaml.
Extraction "factorial.ml" fact.

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `factorial(5) = 120`

**Generated JS — user code only** (from `factorial.js`, 70,418 bytes total, 1,624 shown; runtime prelude elided):

```js
// (js_of_ocaml bundles the entire OCaml runtime + extracted user
//  code into a single closure with mangled identifiers; symbol-
//  based extraction is not feasible. Showing the bundle tail —
//  the verified `fact` is the recursive `function bM(a){ … }`
//  near the end.)
//
// …
m=d[1];if(typeof
e==="number")return e?function(a,b,c){return i(k,[4,j,B(m,a,ag(b,K(f,g,c)))],h)}:function(a,b){return i(k,[4,j,B(m,a,K(f,g,b))],h)};var
o=e[1];return function(a,b){return i(k,[4,j,B(m,a,ag(o,K(f,g,b)))],h)}}function
a7(a,b,c,d,e,f){if(e){var
h=e[1];return function(a){return ds(b,c,d,h,_(f,a))}}var
g=[4,c,f];return a<50?at(a+1|0,b,g,d):ae(at,[0,b,g,d])}function
ds(a,b,c,d,e){return by(a7(0,a,b,c,d,e))}function
S(a,b){var
c=b;for(;;){if(typeof
c==="number")return;switch(c[0]){case
0:var
e=c[2],h=c[1];if(typeof
e==="number")switch(e){case
0:var
d="@]";break;case
1:var
d="@}";break;case
2:var
d="@?";break;case
3:var
d="@\n";break;case
4:var
d="@.";break;case
5:var
d="@@";break;default:var
d="@%"}else
var
d=2===e[0]?"@"+H(Z(1,e[1])):e[1];S(a,h);return aF(a,d);case
1:var
f=c[2],g=c[1];if(0===f[0]){var
i=f[1];S(a,g);aF(a,"@{");c=i}else{var
j=f[1];S(a,g);aF(a,"@[");c=j}break;case
6:var
m=c[2];S(a,c[1]);return _(m,a);case
7:S(a,c[1]);ao(a);return;case
8:var
n=c[2];S(a,c[1]);return aE(n);case
2:case
4:var
k=c[2];S(a,c[1]);return aF(a,k);default:var
l=c[2];S(a,c[1]);ed(a,l);return}}}function
bM(a){return 0===a?1:bv(a,bM(a-1|0))}var
bN=5,dx=bM(bN);K(i(function(a){S(c6,a);return 0},0,[0,[11,"factorial(",[4,0,0,0,[11,") = ",[4,0,0,0,[12,10,0]]]]],"factorial(%d) = %d\n"][1]),bN,dx);bH(0);return}(globalThis));

```
