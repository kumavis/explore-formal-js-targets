# Factorial (with positivity proof)

Recursive factorial function with a proof that the result is at least 1. Dafny uses an SMT-discharged postcondition; Agda and Idris2 use an inductive predicate inhabited by a constructive term.

## Summary

| Language | Source LOC | Source bytes | Compiled bytes | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 31 | 584 | 32,337 | `factorial(5) = 120` | ✅ ok |
| Agda | 40 | 1,343 | 12,424 | `120` | ✅ ok |
| Idris2 | 22 | 619 | 10,221 | `120` | ✅ ok |

## SES compatibility

| Language | Needs bundling | Static scan | `lockdown()` + `require()` | Raw `Compartment.evaluate()` | Bundled (`@endo/bundle-source` → `importBundle`) |
| --- | :---: | :---: | :---: | :---: | :---: |
| Dafny | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ❌ import-failed |
| Agda | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass |
| Idris2 | no | ✅ clean | ✅ pass | ✅ pass | ✅ pass |

### Bundle details

| Language | Bundle bytes (base64) | Imported keys | Notes |
| --- | ---: | --- | --- |
| Dafny | 162,956 | — | import error: `secure mode %SharedMath%.random() throws` |
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

**Generated JS** (`Factorial.js`, 32,337 bytes):

```js
// Dafny program Factorial.dfy compiled into JavaScript
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const BigNumber = require('bignumber.js');
BigNumber.config({ MODULO_MODE: BigNumber.EUCLID })
let _dafny = (function() {
  let $module = {};
  $module.areEqual = function(a, b) {
    if (typeof a === 'string' && b instanceof _dafny.Seq) {
      // Seq.equals(string) works as expected,
      // and the catch-all else block handles that direction.
      // But the opposite direction doesn't work; handle it here.
      return b.equals(a);
    } else if (typeof a === 'number' && BigNumber.isBigNumber(b)) {
      // This conditional would be correct even without the `typeof a` part,
      // but in most cases it's probably faster to short-circuit on a `typeof`
      // than to call `isBigNumber`. (But it remains to properly test this.)
      return b.isEqualTo(a);
    } else if (typeof a !== 'object' || a === null || b === null) {
      return a === b;
    } else if (BigNumber.isBigNumber(a)) {
      return a.isEqualTo(b);
    } else if (a._tname !== undefined || (Array.isArray(a) && a.constructor.name == "Array")) {
      return a === b;  // pointer equality
    } else {
      return a.equals(b);  // value-type equality
    }
  }
  $module.toString = function(a) {
    if (a === null) {
      return "null";
    } else if (typeof a === "number") {
      return a.toFixed();
    } else if (BigNumber.isBigNumber(a)) {
      return a.toFixed();
    } else if (a._tname !== undefined) {
      return a._tname;
    } else {
      return a.toString();
    }
  }
  $module.escapeCharacter = function(cp) {
    let s = String.fromCodePoint(cp.value)
    switch (s) {
      case '\n': return "\\n";
      case '\r': return "\\r";
      case '\t': return "\\t";
      case '\0': return "\\0";
      case '\'': return "\\'";
      case '\"': return "\\\"";
      case '\\': return "\\\\";
      default: return s;
    };
  }
  $module.NewObject = function() {
    return { _tname: "object" };
  }
  $module.InstanceOfTrait = function(obj, trait) {
    return obj._parentTraits !== undefined && obj._parentTraits().includes(trait);
  }
  $module.Rtd_bool = class {
    static get Default() { return false; }
  }
  $module.Rtd_char = class {
    static get Default() { return 'D'; }  // See CharType.DefaultValue in Dafny source code
  }
  $module.Rtd_codepoint = class {
    static get Default() { return new _dafny.CodePoint('D'.codePointAt(0)); }
  }
  $module.Rtd_int = class {
    static get Default() { return BigNumber(0); }
  }
  $module.Rtd_number = class {
    static get Default() { return 0; }
  }
  $module.Rtd_ref = class {
    static get Default() { return null; }
  }
  $module.Rtd_array = class {
    static get Default() { return []; }
  }
  $module.ZERO = new BigNumber(0);
  $module.ONE = new BigNumber(1);
  $module.NUMBER_LIMIT = new BigNumber(0x20).multipliedBy(0x1000000000000);  // 2^53
  $module.Tuple = class Tuple extends Array {
    constructor(...elems) {
      super(...elems);
    }
    toString() {
      return "(" + arrayElementsToString(this) + ")";
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      for (let i = 0; i < this.length; i++) {
        if (!_dafny.areEqual(this[i], other[i])) {
          return false;
        }
      }
      return true;
    }
    static Default(...values) {
      return Tuple.of(...values);
    }
    static Rtd(...rtdArgs) {
      return {
        Default: Tuple.from(rtdArgs, rtd => rtd.Default)
      };
    }
  }
  $module.Set = class Set extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return Set.Empty;
    }
    toString() {
      return "{" + arrayElementsToString(this) + "}";
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new Set();
      }
      return this._empty;
    }
    static fromElements(...elmts) {
      let s = new Set();
      for (let
// ... truncated (28337 more bytes)
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

**Generated JS** (`jAgda.Factorial.js`, 1,593 bytes):

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
exports["main"](a => ({}))

```

**Generated JS** (`agda-rts.js`, 10,831 bytes):

```js
// Contains *most* of the primitives required by the JavaScript backend.
// (Some, e.g., those using Agda types like Maybe, are defined in their
// respective builtin modules.)
//
// Primitives prefixed by 'u' are uncurried variants, which are sometimes
// emitted by the JavaScript backend. Whenever possible, the curried primitives
// should be implemented in terms of the uncurried ones.
//
// Primitives prefixed by '_' are internal variants, usually for those primitives
// which return Agda types like Maybe. These are never emitted by the compiler,
// but can be used internally to define other prefixes.

// Integers

// primIntegerFromString : String -> Int
exports.primIntegerFromString = BigInt;

// primShowInteger : Int -> String
exports.primShowInteger = x => x.toString();

// uprimIntegerPlus : (Int, Int) -> Int
exports.uprimIntegerPlus = (x, y) => x + y;

// uprimIntegerMinus : (Int, Int) -> Int
exports.uprimIntegerMinus = (x, y) => x - y;

// uprimIntegerMultiply : (Int, Int) -> Int
exports.uprimIntegerMultiply = (x, y) => x * y;

// uprimIntegerRem : (Int, Int) -> Int
exports.uprimIntegerRem = (x, y) => x % y;

// uprimIntegerQuot : (Int, Int) -> Int
exports.uprimIntegerQuot = (x, y) => x / y;

// uprimIntegerEqual : (Int, Int) -> Bool
exports.uprimIntegerEqual = (x, y) => x === y;

// uprimIntegerGreaterOrEqualThan : (Int, Int) -> Bool
exports.uprimIntegerGreaterOrEqualThan = (x, y) => x >= y;

// uprimIntegerLessThan : (Int, Int) -> Bool
exports.uprimIntegerLessThan = (x, y) => x < y;

// Words
const WORD64_MAX_VALUE = 18446744073709552000n;

// primWord64ToNat : Word64 -> Nat
exports.primWord64ToNat = x => x;

// primWord64FromNat : Nat -> Word64
exports.primWord64FromNat = x => x % WORD64_MAX_VALUE;

// uprimWord64Plus : (Word64, Word64) -> Word64
exports.uprimWord64Plus = (x, y) => (x + y) % WORD64_MAX_VALUE;

// uprimWord64Minus : (Word64, Word64) -> Word64
exports.uprimWord64Minus = (x, y) => (x + WORD64_MAX_VALUE - y) % WORD64_MAX_VALUE;

// uprimWord64Multiply : (Word64, Word64) -> Word64
exports.uprimWord64Multiply = (x, y) => (x * y) % WORD64_MAX_VALUE;

// Natural numbers

// primNatMinus : Nat -> Nat -> Nat
exports.primNatMinus = x => y => {
  const z = x - y;
  return z < 0n ? 0n : z;
};

// Floating-point numbers
var _primFloatGreatestCommonFactor = function(x, y) {
    var z;
    x = Math.abs(x);
    y = Math.abs(y);
    while (y) {
        z = x % y;
        x = y;
        y = z;
    }
    return x;
};
exports._primFloatRound = function(x) {
    if (exports.primFloatIsNaN(x) || exports.primFloatIsInfinite(x)) {
        return null;
    }
    else {
        return BigInt(Math.round(x));
    }
};
exports._primFloatFloor = function(x) {
    if (exports.primFloatIsNaN(x) || exports.primFloatIsInfinite(x)) {
        return null;
    }
    else {
        return BigInt(Math.floor(x));
    }
};
exports._primFloatCeiling = function(x) {
    if (exports.primFloatIsNaN(x) || exports.primFloatIsInfinite(x)) {
        return null;
    }
    else {
        return BigInt(Math.ceil(x));
    }
};
exports._primFloatToRatio = function(x) {
    if (exports.primFloatIsNaN(x)) {
        return {numerator: BigInt(0), denominator: BigInt(0)};
    }
    else if (x < 0.0 && exports.primFloatIsInfinite(x)) {
        return {numerator: BigInt(-1), denominator: BigInt(0)};
    }
    else if (x > 0.0 && exports.primFloatIsInfinite(x)) {
        return {numerator: BigInt(1), denominator: BigInt(0)};
    }
    else if (exports.primFloatIsNegativeZero(x)) {
        return {numerator: BigInt(0), denominator: BigInt(1)};
    }
    else if (x == 0.0) {
        return {numerator: BigInt(0), denominator: BigInt(1)};
    }
    else {
        var numerator = Math.round(x*1e9);
        var denominator = 1e9;
        var gcf = _primFloatGreatestCommonFactor(numerator, denominator);
        numerator /= gcf;
        denominator /= gcf;
        return {numerator: BigInt(numerator), denominator: BigInt(denominator)};
    }
};
exports._primFloatDe
// ... truncated (6831 more bytes)
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

**Generated JS** (`factorial`, 10,221 bytes):

```js
#!/usr/bin/env node
class IdrisError extends Error { }

function __prim_js2idris_array(x){
  let acc = { h:0 };

  for (let i = x.length-1; i>=0; i--) {
      acc = { a1:x[i], a2:acc };
  }
  return acc;
}

function __prim_idris2js_array(x){
  const result = Array();
  while (x.h === undefined) {
    result.push(x.a1); x = x.a2;
  }
  return result;
}

function __lazy(thunk) {
  let res;
  return function () {
    if (thunk === undefined) return res;
    res = thunk();
    thunk = undefined;
    return res;
  };
};

function __prim_stringIteratorNew(_str) {
  return 0
}

function __prim_stringIteratorToString(_, str, it, f) {
  return f(str.slice(it))
}

function __prim_stringIteratorNext(str, it) {
  if (it >= str.length)
    return {h: 0};
  else
    return {a1: str.charAt(it), a2: it + 1};
}

function __tailRec(f,ini) {
  let obj = ini;
  while(true){
    switch(obj.h){
      case 0: return obj.a1;
      default: obj = f(obj);
    }
  }
}

const _idrisworld = Symbol('idrisworld')

const _crashExp = x=>{throw new IdrisError(x)}

const _bigIntOfString = s=> {
  try {
    const idx = s.indexOf('.')
    return idx === -1 ? BigInt(s) : BigInt(s.slice(0, idx))
  } catch (e) { return 0n }
}

const _numberOfString = s=> {
  try {
    const res = Number(s);
    return isNaN(res) ? 0 : res;
  } catch (e) { return 0 }
}

const _intOfString = s=> Math.trunc(_numberOfString(s))

const _truncToChar = x=> String.fromCodePoint(
  (x >= 0 && x <= 55295) || (x >= 57344 && x <= 1114111) ? x : 0
)

// Int8
const _truncInt8 = x => {
  const res = x & 0xff;
  return res >= 0x80 ? res - 0x100 : res;
}

const _truncBigInt8 = x => Number(BigInt.asIntN(8, x))

// Euclidian Division
const _div = (a,b) => {
  const q = Math.trunc(a / b)
  const r = a % b
  return r < 0 ? (b > 0 ? q - 1 : q + 1) : q
}

const _divBigInt = (a,b) => {
  const q = a / b
  const r = a % b
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q
}

// Euclidian Modulo
const _mod = (a,b) => {
  const r = a % b
  return r < 0 ? (b > 0 ? r + b : r - b) : r
}

const _modBigInt = (a,b) => {
  const r = a % b
  return r < 0n ? (b > 0n ? r + b : r - b) : r
}

const _add8s = (a,b) => _truncInt8(a + b)
const _sub8s = (a,b) => _truncInt8(a - b)
const _mul8s = (a,b) => _truncInt8(a * b)
const _div8s = (a,b) => _truncInt8(_div(a,b))
const _shl8s = (a,b) => _truncInt8(a << b)
const _shr8s = (a,b) => _truncInt8(a >> b)

// Int16
const _truncInt16 = x => {
  const res = x & 0xffff;
  return res >= 0x8000 ? res - 0x10000 : res;
}

const _truncBigInt16 = x => Number(BigInt.asIntN(16, x))

const _add16s = (a,b) => _truncInt16(a + b)
const _sub16s = (a,b) => _truncInt16(a - b)
const _mul16s = (a,b) => _truncInt16(a * b)
const _div16s = (a,b) => _truncInt16(_div(a,b))
const _shl16s = (a,b) => _truncInt16(a << b)
const _shr16s = (a,b) => _truncInt16(a >> b)

//Int32
const _truncInt32 = x => x & 0xffffffff

const _truncBigInt32 = x => Number(BigInt.asIntN(32, x))

const _add32s = (a,b) => _truncInt32(a + b)
const _sub32s = (a,b) => _truncInt32(a - b)
const _div32s = (a,b) => _truncInt32(_div(a,b))

const _mul32s = (a,b) => {
  const res = a * b;
  if (res <= Number.MIN_SAFE_INTEGER || res >= Number.MAX_SAFE_INTEGER) {
    return _truncInt32((a & 0xffff) * b + (b & 0xffff) * (a & 0xffff0000))
  } else {
    return _truncInt32(res)
  }
}

//Int64
const _truncBigInt64 = x => BigInt.asIntN(64, x)

const _add64s = (a,b) => _truncBigInt64(a + b)
const _sub64s = (a,b) => _truncBigInt64(a - b)
const _mul64s = (a,b) => _truncBigInt64(a * b)
const _shl64s = (a,b) => _truncBigInt64(a << b)
const _div64s = (a,b) => _truncBigInt64(_divBigInt(a,b))
const _shr64s = (a,b) => _truncBigInt64(a >> b)

//Bits8
const _truncUInt8 = x => x & 0xff

const _truncUBigInt8 = x => Number(BigInt.asUintN(8, x))

const _add8u = (a,b) => (a + b) & 0xff
const _sub8u = (a,b) => (a - b) & 0xff
const _mul8u = (a,b) => (a * b) & 0xff
const _div8u = (a,b) => Math.trunc(a / b)
const _shl8u = (a,b) => (a << b) & 0xff
const _shr8u = (a,b) => (a 
// ... truncated (6221 more bytes)
```

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **pass** (exit 0)
