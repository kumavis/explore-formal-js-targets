# Triangular-number closed form (2·Σ n = n·(n+1))

A showcase for **SMT-discharged arithmetic**: Dafny proves the closed form in a four-line lemma because the SMT backend handles the nonlinear step. Idris2 needs a 5-line `rewrite` chain over `Data.Nat` lemmas. Agda, with no algebraic-lemma stdlib in the nixpkgs install, has to prove +-comm, +-assoc, *-suc, *-comm itself first — about 60 lines all-in.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 29 | 744 | 1,598 + 30,839 = 32,437 | `sum(0..10) = 55  (2*sum = 110, n*(n+1) = 110)` | ✅ ok |
| Agda | 116 | 3,658 | 1,780 + 14,926 = 16,706 | `sum(0..10) = 55  (sum+sum = 110, n*(n+1) = 110)` | ✅ ok |
| Idris2 | 44 | 1,334 | 263 + 10,102 = 10,365 | `sum(0..10) = 55  (2*sum = 110, n*(n+1) = 110)` | ✅ ok |

## SES compatibility

| Language | Needs bundling | Static scan | `lockdown()` + `require()` | Raw `Compartment.evaluate()` | Bundled (`@endo/bundle-source` → `importBundle`) | Compartment endowments |
| --- | :---: | :---: | :---: | :---: | :---: | --- |
| Dafny | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass | `console` + `BigNumber` + `Math` |
| Agda | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass | `console` |
| Idris2 | no | ✅ clean | ✅ pass | ✅ pass | ✅ pass | `console` |

> **Dafny bundling requirement:** the bundled compartment passes only with `Math` (in addition to `BigNumber`) endowed. Dafny's emitted runtime calls `bignumber.js`, which invokes `Math.random()` during initialization — SES's secure-mode `Math` removes `random`, so without the endowment the bundle imports fail at load. A real deployment should wrap `Math` rather than passing the host's.

### Bundle details

| Language | Bundle bytes (base64) | Imported keys | Notes |
| --- | ---: | --- | --- |
| Dafny | 163,096 | _dafny, _System, SumFormula, _module, default | imported keys: _dafny, _System, SumFormula, _module, default |
| Agda | 38,236 | sum, natToString, putStrLn, main, default, _++_ | imported keys: sum, natToString, putStrLn, main, default, _++_ |
| Idris2 | 15,552 | sum, default | imported keys: sum, default |

---

## Dafny

**Source** (`problems/sum-formula/dafny/SumFormula.dfy`):

```dafny
// Triangular-number closed form: 2 * sum(0..n) == n * (n + 1).
//
// Dafny dispatches both the recursive definition and the inductive proof
// in a handful of lines because the SMT backend handles the nonlinear
// arithmetic step (`2 * (n + sum(n-1)) == n*n + n` after unfolding the IH).

module SumFormula {

  function Sum(n: nat): nat {
    if n == 0 then 0 else n + Sum(n - 1)
  }

  // The whole closed-form theorem: one induction, SMT does the algebra.
  lemma ClosedForm(n: nat)
    ensures 2 * Sum(n) == n * (n + 1)
  {
    if n == 0 {
    } else {
      ClosedForm(n - 1);
    }
  }

  method Main() {
    var n := 10;
    var s := Sum(n);
    print "sum(0..10) = ", s, "  (2*sum = ", 2 * s, ", n*(n+1) = ", n * (n + 1), ")\n";
  }
}

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `sum(0..10) = 55  (2*sum = 110, n*(n+1) = 110)`

**Generated JS — user code only** (from `SumFormula.js`, 32,437 bytes total, 1,598 shown; runtime prelude elided):

```js
let SumFormula = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "SumFormula._default";
    }
    _parentTraits() {
      return [];
    }
    static Sum(n) {
      let _0___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((n).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_0___accumulator);
        } else {
          _0___accumulator = (_0___accumulator).plus(n);
          let _in0 = (n).minus(_dafny.ONE);
          n = _in0;
          continue TAIL_CALL_START;
        }
      }
    };
    static Main(__noArgsParameter) {
      let _0_n;
      _0_n = new BigNumber(10);
      let _1_s;
      _1_s = SumFormula.__default.Sum(_0_n);
      process.stdout.write((_dafny.Seq.UnicodeFromString("sum(0..10) = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(_1_s));
      process.stdout.write((_dafny.Seq.UnicodeFromString("  (2*sum = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString((new BigNumber(2)).multipliedBy(_1_s)));
      process.stdout.write((_dafny.Seq.UnicodeFromString(", n*(n+1) = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString((_0_n).multipliedBy((_0_n).plus(_dafny.ONE))));
      process.stdout.write((_dafny.Seq.UnicodeFromString(")\n")).toVerbatimString(false));
      return;
    }
  };
  return $module;
})(); // end of module SumFormula

// ... runtime prelude elided ...

_dafny.HandleHaltExceptions(() => SumFormula.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
```

---

## Agda

**Source** (`problems/sum-formula/agda/SumFormula.agda`):

```agda
-- Triangular-number closed form: sum(0..n) + sum(0..n) ≡ n * (n + 1).
--
-- Agda's nixpkgs install ships only Agda.Builtin (no Data.Nat.Properties),
-- so every algebraic identity that Dafny's SMT solver discharges silently
-- has to be proved here by structural induction. The chain is:
--
--   sym, +-zero, +-suc, +-comm, +-assoc, *-suc, *-comm,
--   then the closed-form theorem itself.

module SumFormula where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- --- Tiny equality kit (sym + equational reasoning combinators) ------------

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

-- --- Addition lemmas -------------------------------------------------------

+-zero : (n : Nat) -> n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) rewrite +-zero n = refl

+-suc : (n m : Nat) -> n + suc m ≡ suc (n + m)
+-suc zero    m = refl
+-suc (suc n) m rewrite +-suc n m = refl

+-comm : (n m : Nat) -> n + m ≡ m + n
+-comm zero    m rewrite +-zero m = refl
+-comm (suc n) m rewrite +-suc m n | +-comm n m = refl

+-assoc : (n m k : Nat) -> (n + m) + k ≡ n + (m + k)
+-assoc zero    m k = refl
+-assoc (suc n) m k rewrite +-assoc n m k = refl

-- --- Multiplication lemmas -------------------------------------------------

*-zero : (n : Nat) -> n * 0 ≡ 0
*-zero zero    = refl
*-zero (suc n) rewrite *-zero n = refl

*-suc : (n m : Nat) -> n * suc m ≡ n + n * m
*-suc zero    m = refl
*-suc (suc n) m
  rewrite *-suc n m
        | sym (+-assoc m n (n * m))
        | +-comm m n
        | +-assoc n m (n * m)
        = refl

*-comm : (n m : Nat) -> n * m ≡ m * n
*-comm zero    m rewrite *-zero m = refl
*-comm (suc n) m rewrite *-suc m n | *-comm n m = refl

-- --- The function and theorem ----------------------------------------------

sum : Nat -> Nat
sum zero    = 0
sum (suc n) = suc n + sum n

-- Useful re-association lemma the closed-form proof needs.
-- (a + b) + (c + d) ≡ a + (c + (b + d))
shuffle : (a b c d : Nat) -> (a + b) + (c + d) ≡ a + (c + (b + d))
shuffle a b c d =
  trans (+-assoc a b (c + d))
  (cong (a +_)
    (trans (sym (+-assoc b c d))
    (trans (cong (_+ d) (+-comm b c))
           (+-assoc c b d))))

closedForm : (n : Nat) -> sum n + sum n ≡ n * suc n
closedForm zero = refl
closedForm (suc n)
  -- After `shuffle` and IH, LHS becomes
  --   suc n + (suc n + n * suc n)
  -- which definitionally equals suc (suc (n + (n + n * suc n))).
  -- The RHS suc n * suc (suc n) unfolds to suc (suc (n + n * suc (suc n))),
  -- and *-suc lets us rewrite n * suc (suc n) into n + n * suc n
  -- so both sides agree.
  rewrite shuffle (suc n) (sum n) (suc n) (sum n)
        | closedForm n
        | *-suc n (suc n)
        | +-suc n (n + n * suc n)
        = refl

-- --- Executable entry point -------------------------------------------------

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

postulate
  natToString : Nat -> String
  putStrLn    : String -> IO ⊤
{-# COMPILE JS natToString = function (n) { return n.toString(); } #-}
{-# COMPILE JS putStrLn    = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

infixr 5 _++_
_++_ : String -> String -> String
s ++ t = primStringAppend s t

main : IO ⊤
main = putStrLn (
    "sum(0..10) = "      ++ natToString (sum 10) ++
    "  (sum+sum = "      ++ natToString (sum 10 + sum 10) ++
    ", n*(n+1) = "       ++ natToString (10 * 11) ++ ")"
  )

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `sum(0..10) = 55  (sum+sum = 110, n*(n+1) = 110)`

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

**Generated JS — user code only** (from `jAgda.SumFormula.js`, 1,808 bytes total, 1,780 shown; runtime prelude elided):

```js
var agdaRTS = require("agda-rts");

var z_jAgda_Agda_Builtin_Equality = require("jAgda.Agda.Builtin.Equality");
var z_jAgda_Agda_Builtin_IO = require("jAgda.Agda.Builtin.IO");
var z_jAgda_Agda_Builtin_Nat = require("jAgda.Agda.Builtin.Nat");
var z_jAgda_Agda_Builtin_String = require("jAgda.Agda.Builtin.String");
var z_jAgda_Agda_Builtin_Unit = require("jAgda.Agda.Builtin.Unit");
var z_jAgda_Agda_Primitive = require("jAgda.Agda.Primitive");

exports["sum"] = a => agdaRTS.uprimIntegerEqual(agdaRTS.primIntegerFromString("0"),a)? agdaRTS.primIntegerFromString("0"): (
    b => agdaRTS.uprimIntegerPlus(exports["sum"](b()),a)
  )(
    () => agdaRTS.uprimIntegerMinus(a,agdaRTS.primIntegerFromString("1"))
  );
exports["_++_"] = a => b => z_jAgda_Agda_Builtin_String["primStringAppend"](a)(b);
exports["natToString"] = function (n) { return n.toString(); };
exports["putStrLn"] = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; };
exports["main"] = exports["putStrLn"](
    exports["_++_"]("sum(0..10) = ")(
      exports["_++_"](
        exports["natToString"](
          exports["sum"](agdaRTS.primIntegerFromString("10"))
      ) )(
        exports["_++_"]("  (sum+sum = ")(
          exports["_++_"](
            exports["natToString"](
              agdaRTS.uprimIntegerPlus(
                exports["sum"](agdaRTS.primIntegerFromString("10")),
                exports["sum"](agdaRTS.primIntegerFromString("10"))
          ) ) )(
            exports["_++_"](", n*(n+1) = ")(
              exports["_++_"](
                exports["natToString"](
                  agdaRTS.uprimIntegerMultiply(
                    agdaRTS.primIntegerFromString("10"),
                    agdaRTS.primIntegerFromString("11")
              ) ) )(")")
) ) ) ) ) );
```

---

## Idris2

**Source** (`problems/sum-formula/idris2/SumFormula.idr`):

```idris
||| Triangular-number closed form: 2 * sum(0..n) = n * (n + 1).
|||
||| Idris2 has no SMT backend, so the algebra is *manual*: every step
||| where Dafny waves its hand at nonlinear arithmetic becomes an explicit
||| chain of rewrites using lemmas from `Data.Nat`.

module SumFormula

import Data.Nat
import Data.Nat.Views

%default total

sum : Nat -> Nat
sum Z     = 0
sum (S n) = (S n) + sum n

-- Goal: 2 * sum n = n * (S n)
--
-- Inductive step on (S n):
--   2 * sum (S n)
--     = 2 * (S n + sum n)                      [def of sum]
--     = 2 * S n + 2 * sum n                    [left distrib]
--     = 2 * S n + n * S n                      [IH]
--     = (2 + n) * S n                          [right distrib backwards]
--     = S (S n) * S n                          [def of +]
--     = S n * S (S n)                          [* commutativity]

closedForm : (n : Nat) -> 2 * sum n = n * (S n)
closedForm Z = Refl
closedForm (S n) =
  let ih = closedForm n in
  rewrite multDistributesOverPlusRight 2 (S n) (sum n) in
  rewrite ih in
  rewrite sym (multDistributesOverPlusLeft 2 n (S n)) in
  rewrite multCommutative (2 + n) (S n) in
  Refl

main : IO ()
main = do
  let n = 10
  let s = SumFormula.sum n
  putStrLn ("sum(0..10) = " ++ show s ++ "  (2*sum = " ++ show (2 * s) ++ ", n*(n+1) = " ++ show (n * (n + 1)) ++ ")")

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `sum(0..10) = 55  (2*sum = 110, n*(n+1) = 110)`

**Generated JS — user code only** (from `sumformula`, 10,365 bytes total, 263 shown; runtime prelude elided):

```js
function SumFormula_sum($0) {
 switch($0) {
  case 0n: return 0n;
  default: {
   const $2 = ($0-1n);
   return (($2+1n)+SumFormula_sum($2));
  }
 }
}
try{__mainExpression_0()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }
```
