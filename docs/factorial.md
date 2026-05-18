# Factorial (with positivity proof)

Recursive factorial function with a proof that the result is at least 1. Dafny uses an SMT-discharged postcondition; Agda and Idris2 use an inductive predicate inhabited by a constructive term.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 31 | 584 | 1,499 + 30,838 = 32,337 | `factorial(5) = 120` | ✅ ok |
| Agda | 40 | 1,343 | 1,565 + 14,926 = 16,491 | `120` | ✅ ok |
| Idris2 | 22 | 619 | 403 + 9,818 = 10,221 | `120` | ✅ ok |

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
| Dafny | 162,956 | _dafny, _System, Factorial, _module, default | imported keys: _dafny, _System, Factorial, _module, default |
| Agda | 37,948 | IsPositive, factorial, natToString, putStrLn, main, default, mul-pos, factorial-pos | imported keys: IsPositive, factorial, natToString, putStrLn, main, default, mul-pos, factorial-pos |
| Idris2 | 15,380 | factorial, default | imported keys: factorial, default |

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

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **evaluate-failed** (exit 4)
  - stderr: `EVALUATE_FAILED: require is not a function`

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

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **evaluate-failed** (exit 4)
  - stderr: `EVALUATE_FAILED: require is not a function`

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

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **pass** (exit 0)
