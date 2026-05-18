# Insertion sort (with sortedness proof)

Insertion sort over a list of naturals. Dafny verifies both sortedness AND multiset-preservation (a true permutation proof). Agda and Idris2 verify sortedness via an inductive Sorted predicate and dependent transitivity lemmas.

## Summary

| Language | Source LOC | Source bytes | Compiled bytes | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 78 | 2,211 | 32,545 | `sort([3,1,4,1,5,9,2,6]) = [1, 1, 2, 3, 4, 5, 6, 9]` | ✅ ok |
| Agda | 92 | 3,500 | 16,957 | `[1,1,2,3,4,5,6,9]` | ✅ ok |
| Idris2 | 79 | 3,051 | 12,317 | `[1, 1, 2, 3, 4, 5, 6, 9]` | ✅ ok |

## SES compatibility

| Language | Static findings | `lockdown()` + `require()` | `Compartment.evaluate()` |
| --- | --- | --- | --- |
| Dafny | none | pass | evaluate-failed |
| Agda | none | pass | evaluate-failed |
| Idris2 | none | pass | pass |

---

## Dafny

**Source** (`problems/insertion-sort/dafny/InsertionSort.dfy`):

```dafny
// Insertion sort verified to (a) produce a sorted sequence and
// (b) preserve the multiset of elements (i.e. it's a permutation).
// Both properties are discharged automatically by Dafny's SMT backend.

module InsertionSort {

  ghost predicate Sorted(xs: seq<int>)
  {
    forall i, j :: 0 <= i <= j < |xs| ==> xs[i] <= xs[j]
  }

  function Insert(x: int, xs: seq<int>): (r: seq<int>)
    requires Sorted(xs)
    ensures Sorted(r)
    ensures multiset(r) == multiset(xs) + multiset{x}
  {
    if |xs| == 0 then [x]
    else if x <= xs[0] then
      assert Sorted([x] + xs) by {
        forall i, j | 0 <= i <= j < |[x] + xs|
          ensures ([x] + xs)[i] <= ([x] + xs)[j]
        {
          if i == 0 {
            if j == 0 {
            } else {
              assert ([x] + xs)[j] == xs[j-1];
              assert x <= xs[0] <= xs[j-1];
            }
          } else {
            assert ([x] + xs)[i] == xs[i-1];
            assert ([x] + xs)[j] == xs[j-1];
          }
        }
      }
      [x] + xs
    else
      var rest := Insert(x, xs[1..]);
      assert xs == [xs[0]] + xs[1..];
      assert multiset(xs) == multiset{xs[0]} + multiset(xs[1..]);
      assert Sorted([xs[0]] + rest) by {
        forall i, j | 0 <= i <= j < |[xs[0]] + rest|
          ensures ([xs[0]] + rest)[i] <= ([xs[0]] + rest)[j]
        {
          if i == 0 {
            if j == 0 {
            } else {
              var v := ([xs[0]] + rest)[j];
              assert v == rest[j-1];
              assert v in multiset(rest);
              assert multiset(rest) == multiset(xs[1..]) + multiset{x};
              assert v in multiset(xs[1..]) || v == x;
            }
          } else {
            assert ([xs[0]] + rest)[i] == rest[i-1];
            assert ([xs[0]] + rest)[j] == rest[j-1];
          }
        }
      }
      [xs[0]] + rest
  }

  function Sort(xs: seq<int>): (r: seq<int>)
    ensures Sorted(r)
    ensures multiset(r) == multiset(xs)
  {
    if |xs| == 0 then []
    else
      assert xs == [xs[0]] + xs[1..];
      Insert(xs[0], Sort(xs[1..]))
  }

  method Main() {
    var xs := [3, 1, 4, 1, 5, 9, 2, 6];
    var sorted := Sort(xs);
    print "sort([3,1,4,1,5,9,2,6]) = ", sorted, "\n";
  }
}

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `sort([3,1,4,1,5,9,2,6]) = [1, 1, 2, 3, 4, 5, 6, 9]`

**Generated JS** (`InsertionSort.js`, 32,545 bytes):

```js
// Dafny program InsertionSort.dfy compiled into JavaScript
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
      for 
// ... truncated (28545 more bytes)
```

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **evaluate-failed** (exit 4)
  - stderr: `EVALUATE_FAILED: require is not a function`

---

## Agda

**Source** (`problems/insertion-sort/agda/InsertionSort.agda`):

```agda
-- Insertion sort with a sortedness proof.
-- Sortedness is a *type-level* predicate; the proof is a constructive term
-- that the type checker verifies as well-formed.

module InsertionSort where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

-- ≤ on naturals as an inductive family.
data _≤_ : Nat -> Nat -> Set where
  z≤n : {n : Nat}             -> zero ≤ n
  s≤s : {m n : Nat} -> m ≤ n  -> suc m ≤ suc n

-- ≤ is transitive.
≤-trans : {a b c : Nat} -> a ≤ b -> b ≤ c -> a ≤ c
≤-trans z≤n       _         = z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

-- A decidable comparison: either x ≤ y, or y ≤ x.
data Order (x y : Nat) : Set where
  le : x ≤ y -> Order x y
  gt : y ≤ x -> Order x y

compare : (x y : Nat) -> Order x y
compare zero    y       = le z≤n
compare (suc x) zero    = gt z≤n
compare (suc x) (suc y) with compare x y
... | le p = le (s≤s p)
... | gt p = gt (s≤s p)

-- Predicate "x is ≤ every element of xs".
data _≤*_ (x : Nat) : List Nat -> Set where
  []  : x ≤* []
  _∷_ : {y : Nat} {ys : List Nat} -> x ≤ y -> x ≤* ys -> x ≤* (y ∷ ys)

-- Sortedness as an inductive proposition.
data Sorted : List Nat -> Set where
  []  : Sorted []
  _∷_ : {x : Nat} {xs : List Nat} -> x ≤* xs -> Sorted xs -> Sorted (x ∷ xs)

-- If x ≤ y and y is below all of xs, then x is below all of xs.
≤*-trans : {x y : Nat} {xs : List Nat} -> x ≤ y -> y ≤* xs -> x ≤* xs
≤*-trans x≤y []             = []
≤*-trans x≤y (y≤z ∷ y≤*rest) = ≤-trans x≤y y≤z ∷ ≤*-trans x≤y y≤*rest

-- Insertion into a list (no proof obligation at the value level).
insert : Nat -> List Nat -> List Nat
insert x []       = x ∷ []
insert x (y ∷ ys) with compare x y
... | le _ = x ∷ y ∷ ys
... | gt _ = y ∷ insert x ys

-- Lemma: insert preserves the "lo ≤ every elem" predicate.
insert-≤* : {lo x : Nat} {xs : List Nat}
          -> lo ≤ x -> lo ≤* xs -> lo ≤* insert x xs
insert-≤* {lo} {x} {[]}     lo≤x []                = lo≤x ∷ []
insert-≤* {lo} {x} {y ∷ ys} lo≤x (lo≤y ∷ lo≤*rest) with compare x y
... | le _ = lo≤x ∷ lo≤y ∷ lo≤*rest
... | gt _ = lo≤y ∷ insert-≤* lo≤x lo≤*rest

-- Theorem: insert preserves sortedness.
insert-sorted : (x : Nat) (xs : List Nat) -> Sorted xs -> Sorted (insert x xs)
insert-sorted x []       []                = [] ∷ []
insert-sorted x (y ∷ ys) (y≤*ys ∷ s-ys) with compare x y
... | le x≤y = (x≤y ∷ ≤*-trans x≤y y≤*ys) ∷ (y≤*ys ∷ s-ys)
... | gt y≤x = insert-≤* y≤x y≤*ys ∷ insert-sorted x ys s-ys

-- The sort function.
sort : List Nat -> List Nat
sort []       = []
sort (x ∷ xs) = insert x (sort xs)

-- Theorem: sort always returns a sorted list.
sort-sorted : (xs : List Nat) -> Sorted (sort xs)
sort-sorted []       = []
sort-sorted (x ∷ xs) = insert-sorted x (sort xs) (sort-sorted xs)

-- Executable main.
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

postulate
  showList : List Nat -> String
  putStrLn : String -> IO ⊤
{-# COMPILE JS showList = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; } #-}
{-# COMPILE JS putStrLn = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (showList (sort (3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 9 ∷ 2 ∷ 6 ∷ [])))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `[1,1,2,3,4,5,6,9]`

**Generated JS** (`jAgda.InsertionSort.js`, 6,126 bytes):

```js
var agdaRTS = require("agda-rts");

var z_jAgda_Agda_Builtin_IO = require("jAgda.Agda.Builtin.IO");
var z_jAgda_Agda_Builtin_List = require("jAgda.Agda.Builtin.List");
var z_jAgda_Agda_Builtin_Nat = require("jAgda.Agda.Builtin.Nat");
var z_jAgda_Agda_Builtin_String = require("jAgda.Agda.Builtin.String");
var z_jAgda_Agda_Builtin_Unit = require("jAgda.Agda.Builtin.Unit");
var z_jAgda_Agda_Primitive = require("jAgda.Agda.Primitive");

exports["_≤_"] = {};
exports["Order"] = {};
exports["_≤*_"] = {};
exports["Sorted"] = {};
exports["_≤_"]["z≤n"] = a => b => b["z≤n"](a);
exports["_≤_"]["s≤s"] = a => b => c => d => d["s≤s"](a,b,c);
exports["≤-trans"] = a => b => c => d => e => d({
    "s≤s": (f,g,h) => e({
      "s≤s": (i,j,k) => exports["_≤_"]["s≤s"](null)(null)(
        exports["≤-trans"](null)(null)(null)(h)(k)
      )
    }),
    "z≤n": f => exports["_≤_"]["z≤n"](null)
  });
exports["Order"]["le"] = a => b => b["le"](a);
exports["Order"]["gt"] = a => b => b["gt"](a);
exports["compare"] = a => b => agdaRTS.uprimIntegerEqual(agdaRTS.primIntegerFromString("0"),a)? exports["Order"]["le"](exports["_≤_"]["z≤n"](null)): (
    c => agdaRTS.uprimIntegerEqual(agdaRTS.primIntegerFromString("0"),b)? exports["Order"]["gt"](exports["_≤_"]["z≤n"](null)): (
    d => (
    e => e()({
    "gt": f => exports["Order"]["gt"](exports["_≤_"]["s≤s"](null)(null)(f)),
    "le": f => exports["Order"]["le"](exports["_≤_"]["s≤s"](null)(null)(f))
  })
  )(() => exports["compare"](c())(d()))
  )(
    () => agdaRTS.uprimIntegerMinus(b,agdaRTS.primIntegerFromString("1"))
  )
  )(
    () => agdaRTS.uprimIntegerMinus(a,agdaRTS.primIntegerFromString("1"))
  );
exports["_≤*_"]["[]"] = a => a["[]"]();
exports["_≤*_"]["_∷_"] = a => b => c => d => e => e["_∷_"](a,b,c,d);
exports["Sorted"]["[]"] = a => a["[]"]();
exports["Sorted"]["_∷_"] = a => b => c => d => e => e["_∷_"](a,b,c,d);
exports["≤*-trans"] = a => b => c => d => e => e({
    "[]": () => e,
    "_∷_": (f,g,h,i) => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
      c,
      {
        "_∷_": (j,k) => exports["_≤*_"]["_∷_"](null)(null)(
          exports["≤-trans"](null)(null)(null)(d)(h)
        )(
          exports["≤*-trans"](null)(null)(k)(d)(i)
    ) } )
  });
exports["insert"] = a => b => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    b,
    {
      "[]": () => z_jAgda_Agda_Builtin_List["List"]["_∷_"](a)(b),
      "_∷_": (c,d) => (
        e => e()({
        "gt": f => z_jAgda_Agda_Builtin_List["List"]["_∷_"](c)(exports["insert"](a)(d)),
        "le": f => z_jAgda_Agda_Builtin_List["List"]["_∷_"](a)(b)
      })
      )(() => exports["compare"](a)(c))
  } );
exports["insert-≤*"] = a => b => c => d => e => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    c,
    {
      "[]": () => agdaRTS.primSeq(
        e,
        exports["_≤*_"]["_∷_"](null)(null)(d)(exports["_≤*_"]["[]"])
      ),
      "_∷_": (f,g) => e({
        "_∷_": (h,i,j,k) => (
          l => l()({
          "gt": m => exports["_≤*_"]["_∷_"](null)(null)(j)(
            exports["insert-≤*"](null)(b)(g)(d)(k)
          ),
          "le": m => exports["_≤*_"]["_∷_"](null)(null)(d)(
            exports["_≤*_"]["_∷_"](null)(null)(j)(k)
          )
        })
        )(() => exports["compare"](b)(f))
  }) } );
exports["insert-sorted"] = a => b => c => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    b,
    {
      "[]": () => agdaRTS.primSeq(
        c,
        exports["Sorted"]["_∷_"](null)(null)(exports["_≤*_"]["[]"])(exports["Sorted"]["[]"])
      ),
      "_∷_": (d,e) => c({
        "_∷_": (f,g,h,i) => (
          j => j()({
          "gt": k => exports["Sorted"]["_∷_"](null)(null)(
            exports["insert-≤*"](null)(a)(e)(k)(h)
          )(exports["insert-sorted"](a)(e)(i)),
          "le": k => exports["Sorted"
// ... truncated (1962 more bytes)
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

**Source** (`problems/insertion-sort/idris2/InsertionSort.idr`):

```idris
||| Insertion sort with a sortedness proof.
||| Sortedness is a *type-level* predicate; the proof is a constructive term
||| that Idris2's type checker verifies as well-formed.

module InsertionSort

import Data.Nat

%default total

-- A locally-defined transitivity on LTE that pattern matches enough to
-- bring the otherwise-erased indices into runtime scope.
lteTrans : {0 a, b, c : Nat} -> LTE a b -> LTE b c -> LTE a c
lteTrans LTEZero       _              = LTEZero
lteTrans (LTESucc ab) (LTESucc bc)    = LTESucc (lteTrans ab bc)

-- Decidable comparison built on Data.Nat.LTE.
data Order' : Nat -> Nat -> Type where
  Le : LTE x y -> Order' x y
  Gt : LTE y x -> Order' x y

compare' : (x, y : Nat) -> Order' x y
compare' Z     y     = Le LTEZero
compare' (S _) Z     = Gt LTEZero
compare' (S x) (S y) = case compare' x y of
                         Le p => Le (LTESucc p)
                         Gt p => Gt (LTESucc p)

-- "x is ≤ every element of xs".
data LowerBound : Nat -> List Nat -> Type where
  LB_Nil  : LowerBound x []
  LB_Cons : LTE x y -> LowerBound x ys -> LowerBound x (y :: ys)

-- Sortedness.
data Sorted : List Nat -> Type where
  S_Nil  : Sorted []
  S_Cons : LowerBound x xs -> Sorted xs -> Sorted (x :: xs)

-- If x ≤ y and y ≤* xs, then x ≤* xs.
lbTrans : {0 x, y : Nat} -> {0 xs : List Nat}
       -> LTE x y -> LowerBound y xs -> LowerBound x xs
lbTrans _   LB_Nil           = LB_Nil
lbTrans xy (LB_Cons yz rest) = LB_Cons (lteTrans xy yz) (lbTrans xy rest)

-- Value-level insertion.
insert : Nat -> List Nat -> List Nat
insert x []        = x :: []
insert x (y :: ys) = case compare' x y of
                       Le _ => x :: y :: ys
                       Gt _ => y :: insert x ys

-- Lemma: insert preserves "lo ≤ everything".
insertLB : {0 lo : Nat} -> (x : Nat) -> {xs : List Nat}
        -> LTE lo x -> LowerBound lo xs -> LowerBound lo (insert x xs)
insertLB x {xs = []}        loX LB_Nil          = LB_Cons loX LB_Nil
insertLB x {xs = (y :: ys)} loX (LB_Cons loY rest) with (compare' x y)
  insertLB x {xs = (y :: ys)} loX (LB_Cons loY rest) | Le _ = LB_Cons loX (LB_Cons loY rest)
  insertLB x {xs = (y :: ys)} loX (LB_Cons loY rest) | Gt _ = LB_Cons loY (insertLB x loX rest)

-- Theorem: insert preserves sortedness.
insertSorted : (x : Nat) -> (xs : List Nat) -> Sorted xs -> Sorted (insert x xs)
insertSorted x []        S_Nil           = S_Cons LB_Nil S_Nil
insertSorted x (y :: ys) (S_Cons lb syss) with (compare' x y)
  insertSorted x (y :: ys) (S_Cons lb syss) | Le xy = S_Cons (LB_Cons xy (lbTrans xy lb)) (S_Cons lb syss)
  insertSorted x (y :: ys) (S_Cons lb syss) | Gt yx = S_Cons (insertLB x yx lb) (insertSorted x ys syss)

-- The sort function.
sort : List Nat -> List Nat
sort []        = []
sort (x :: xs) = insert x (sort xs)

-- Theorem: sort always returns a sorted list.
sortSorted : (xs : List Nat) -> Sorted (sort xs)
sortSorted []        = S_Nil
sortSorted (x :: xs) = insertSorted x (sort xs) (sortSorted xs)

main : IO ()
main = printLn (sort [3, 1, 4, 1, 5, 9, 2, 6])

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `[1, 1, 2, 3, 4, 5, 6, 9]`

**Generated JS** (`insertionsort`, 12,317 bytes):

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
// ... truncated (8317 more bytes)
```

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **pass** (exit 0)
