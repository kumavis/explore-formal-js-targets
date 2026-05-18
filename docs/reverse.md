# List reverse (with reverse-reverse-identity proof)

Naive list reverse with the theorem reverse(reverse(xs)) ≡ xs. Dafny proves it with SMT and a couple of induction lemmas; Agda and Idris2 prove it with structural induction and rewrite tactics.

## Summary

| Language | Source LOC | Source bytes | Compiled bytes | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 38 | 792 | 32,211 | `reverse([1,2,3,4]) = [4, 3, 2, 1]` | ✅ ok |
| Agda | 60 | 2,178 | 12,763 | `[4,3,2,1]` | ✅ ok |
| Idris2 | 34 | 1,160 | 11,850 | `[4, 3, 2, 1]` | ✅ ok |

## SES compatibility

| Language | Needs bundling | Static scan | `lockdown()` + `require()` | Raw `Compartment.evaluate()` | Bundled (`@endo/bundle-source` → `importBundle`) |
| --- | :---: | :---: | :---: | :---: | :---: |
| Dafny | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ❌ import-failed |
| Agda | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass |
| Idris2 | no | ✅ clean | ✅ pass | ✅ pass | ✅ pass |

### Bundle details

| Language | Bundle bytes (base64) | Imported keys | Notes |
| --- | ---: | --- | --- |
| Dafny | 162,760 | — | import error: `secure mode %SharedMath%.random() throws` |
| Agda | 38,456 | reverse, showList, putStrLn, main, default, _++_ | imported keys: reverse, showList, putStrLn, main, default, _++_ |
| Idris2 | 17,596 | reverse, default | imported keys: reverse, default |

---

## Dafny

**Source** (`problems/reverse/dafny/Reverse.dfy`):

```dafny
// List reverse with proof that reverse is involutive: rev(rev(xs)) == xs.
// Two helper lemmas, one main theorem; SMT-discharged induction.

module Reverse {

  function Rev<T>(xs: seq<T>): seq<T>
  {
    if |xs| == 0 then [] else Rev(xs[1..]) + [xs[0]]
  }

  lemma RevAppend<T>(xs: seq<T>, ys: seq<T>)
    ensures Rev(xs + ys) == Rev(ys) + Rev(xs)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      assert (xs + ys)[1..] == xs[1..] + ys;
      RevAppend(xs[1..], ys);
    }
  }

  lemma RevRev<T>(xs: seq<T>)
    ensures Rev(Rev(xs)) == xs
  {
    if |xs| == 0 {
    } else {
      RevRev(xs[1..]);
      RevAppend(Rev(xs[1..]), [xs[0]]);
    }
  }

  method Main() {
    var xs := [1, 2, 3, 4];
    var ys := Rev(xs);
    print "reverse([1,2,3,4]) = ", ys, "\n";
  }
}

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `reverse([1,2,3,4]) = [4, 3, 2, 1]`

**Generated JS** (`Reverse.js`, 32,211 bytes):

```js
// Dafny program Reverse.dfy compiled into JavaScript
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
      for (let k
// ... truncated (28211 more bytes)
```

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **evaluate-failed** (exit 4)
  - stderr: `EVALUATE_FAILED: require is not a function`

---

## Agda

**Source** (`problems/reverse/agda/Reverse.agda`):

```agda
-- List reverse with proof that reverse is involutive: reverse (reverse xs) ≡ xs.
-- Uses propositional equality and structural induction.

module Reverse where

open import Agda.Builtin.List
open import Agda.Builtin.Equality

-- Append (++) -- not a builtin, so we define it here.
infixr 5 _++_
_++_ : {A : Set} -> List A -> List A -> List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Standard naive reverse: O(n²) but easy to reason about.
reverse : {A : Set} -> List A -> List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

-- Lemma: ++ is associative.
++-assoc : {A : Set} (xs ys zs : List A)
         -> (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

-- Lemma: xs ++ [] ≡ xs.
++-[] : {A : Set} (xs : List A) -> xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) rewrite ++-[] xs = refl

-- Lemma: reverse distributes over append (with a flip).
reverse-++ : {A : Set} (xs ys : List A)
           -> reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ []       ys rewrite ++-[] (reverse ys) = refl
reverse-++ (x ∷ xs) ys rewrite reverse-++ xs ys
                              | ++-assoc (reverse ys) (reverse xs) (x ∷ [])
                              = refl

-- Theorem: reverse is its own inverse.
reverse-reverse : {A : Set} (xs : List A) -> reverse (reverse xs) ≡ xs
reverse-reverse []       = refl
reverse-reverse (x ∷ xs) rewrite reverse-++ (reverse xs) (x ∷ [])
                                | reverse-reverse xs
                                = refl

-- Executable entry point.
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Nat
open import Agda.Builtin.String

postulate
  showList    : List Nat -> String
  putStrLn    : String -> IO ⊤
{-# COMPILE JS showList = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; } #-}
{-# COMPILE JS putStrLn = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (showList (reverse (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `[4,3,2,1]`

**Generated JS** (`jAgda.Reverse.js`, 1,932 bytes):

```js
var agdaRTS = require("agda-rts");

var z_jAgda_Agda_Builtin_Equality = require("jAgda.Agda.Builtin.Equality");
var z_jAgda_Agda_Builtin_IO = require("jAgda.Agda.Builtin.IO");
var z_jAgda_Agda_Builtin_List = require("jAgda.Agda.Builtin.List");
var z_jAgda_Agda_Builtin_Nat = require("jAgda.Agda.Builtin.Nat");
var z_jAgda_Agda_Builtin_String = require("jAgda.Agda.Builtin.String");
var z_jAgda_Agda_Builtin_Unit = require("jAgda.Agda.Builtin.Unit");
var z_jAgda_Agda_Primitive = require("jAgda.Agda.Primitive");

exports["_++_"] = a => b => c => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    b,
    {
      "[]": () => c,
      "_∷_": (d,e) => z_jAgda_Agda_Builtin_List["List"]["_∷_"](d)(exports["_++_"](null)(e)(c))
  } );
exports["reverse"] = a => b => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    b,
    {
      "[]": () => b,
      "_∷_": (c,d) => exports["_++_"](null)(exports["reverse"](null)(d))(
        z_jAgda_Agda_Builtin_List["List"]["_∷_"](c)(
          z_jAgda_Agda_Builtin_List["List"]["[]"]
  ) ) } );
exports["showList"] = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; };
exports["putStrLn"] = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; };
exports["main"] = exports["putStrLn"](
    exports["showList"](
      exports["reverse"](null)(
        z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("1"))(
          z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("2"))(
            z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("3"))(
              z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("4"))(
                z_jAgda_Agda_Builtin_List["List"]["[]"]
) ) ) ) ) ) );
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

**Source** (`problems/reverse/idris2/Reverse.idr`):

```idris
||| List reverse with proof that reverse is involutive: reverse (reverse xs) = xs.
||| Uses propositional equality (Refl) and rewrite tactics.

module Reverse

%default total

myReverse : List a -> List a
myReverse []        = []
myReverse (x :: xs) = myReverse xs ++ [x]

appendNilRight : (xs : List a) -> xs ++ [] = xs
appendNilRight []        = Refl
appendNilRight (x :: xs) = rewrite appendNilRight xs in Refl

appendAssoc : (xs, ys, zs : List a) -> (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssoc []        ys zs = Refl
appendAssoc (x :: xs) ys zs = rewrite appendAssoc xs ys zs in Refl

reverseAppend : (xs, ys : List a) -> myReverse (xs ++ ys) = myReverse ys ++ myReverse xs
reverseAppend []        ys = rewrite appendNilRight (myReverse ys) in Refl
reverseAppend (x :: xs) ys =
  rewrite reverseAppend xs ys in
  rewrite appendAssoc (myReverse ys) (myReverse xs) [x] in Refl

reverseReverse : (xs : List a) -> myReverse (myReverse xs) = xs
reverseReverse []        = Refl
reverseReverse (x :: xs) =
  rewrite reverseAppend (myReverse xs) [x] in
  rewrite reverseReverse xs in Refl

main : IO ()
main = printLn (myReverse (the (List Int) [1, 2, 3, 4]))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `[4, 3, 2, 1]`

**Generated JS** (`reverse`, 11,850 bytes):

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
// ... truncated (7850 more bytes)
```

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **pass** (exit 0)
