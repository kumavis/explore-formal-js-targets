# Insertion sort (with sortedness proof)

Insertion sort over a list of naturals. Dafny verifies both sortedness AND multiset-preservation (a true permutation proof). Agda and Idris2 verify sortedness via an inductive Sorted predicate and dependent transitivity lemmas.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 78 | 2,211 | 1,703 + 30,842 = 32,545 | `sort([3,1,4,1,5,9,2,6]) = [1, 1, 2, 3, 4, 5, 6, 9]` | ✅ ok |
| Agda | 92 | 3,500 | 6,098 + 14,759 = 20,857 | `[1,1,2,3,4,5,6,9]` | ✅ ok |
| Idris2 | 79 | 3,051 | 1,477 + 10,840 = 12,317 | `[1, 1, 2, 3, 4, 5, 6, 9]` | ✅ ok |

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
| Dafny | 163,256 | _dafny, _System, InsertionSort, _module, default | sort output matches expected |
| Agda | 43,452 | Order, Sorted, compare, insert, sort, showList, putStrLn, main, default, _≤_, _≤*_, ≤-trans, ≤*-trans, insert-≤*, insert-sorted, sort-sorted | sort output matches expected |
| Idris2 | 18,240 | sort, default | sort output matches expected |

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

**Generated JS — user code only** (from `InsertionSort.js`, 32,545 bytes total, 1,703 shown; runtime prelude elided):

```js
let InsertionSort = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "InsertionSort._default";
    }
    _parentTraits() {
      return [];
    }
    static Insert(x, xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of(x);
      } else if ((x).isLessThanOrEqualTo((xs)[_dafny.ZERO])) {
        return _dafny.Seq.Concat(_dafny.Seq.of(x), xs);
      } else {
        let _0_rest = InsertionSort.__default.Insert(x, (xs).slice(_dafny.ONE));
        return _dafny.Seq.Concat(_dafny.Seq.of((xs)[_dafny.ZERO]), _0_rest);
      }
    };
    static Sort(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of();
      } else {
        return InsertionSort.__default.Insert((xs)[_dafny.ZERO], InsertionSort.__default.Sort((xs).slice(_dafny.ONE)));
      }
    };
    static Main(__noArgsParameter) {
      let _0_xs;
      _0_xs = _dafny.Seq.of(new BigNumber(3), _dafny.ONE, new BigNumber(4), _dafny.ONE, new BigNumber(5), new BigNumber(9), new BigNumber(2), new BigNumber(6));
      let _1_sorted;
      _1_sorted = InsertionSort.__default.Sort(_0_xs);
      process.stdout.write((_dafny.Seq.UnicodeFromString("sort([3,1,4,1,5,9,2,6]) = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(_1_sorted));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
  };
  return $module;
})(); // end of module InsertionSort

// ... runtime prelude elided ...

_dafny.HandleHaltExceptions(() => InsertionSort.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
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

*(`agda-rts.js`, 10,831 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Bool.js`, 187 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Char.js`, 743 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.IO.js`, 126 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.List.js`, 250 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Maybe.js`, 224 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Nat.js`, 500 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Sigma.js`, 295 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.String.js`, 1,281 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Builtin.Unit.js`, 139 bytes — runtime / stdlib, elided)*

*(`jAgda.Agda.Primitive.js`, 155 bytes — runtime / stdlib, elided)*

**Generated JS — user code only** (from `jAgda.InsertionSort.js`, 6,126 bytes total, 6,098 shown; runtime prelude elided):

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
          "le": k => exports["Sorted"]["_∷_"](null)(null)(
            exports["_≤*_"]["_∷_"](null)(null)(k)(
              exports["≤*-trans"](null)(null)(e)(k)(h)
          ) )(
            exports["Sorted"]["_∷_"](null)(null)(h)(i)
          )
        })
        )(() => exports["compare"](a)(d))
  }) } );
exports["sort"] = a => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    a,
    {
      "[]": () => a,
      "_∷_": (b,c) => exports["insert"](b)(exports["sort"](c))
  } );
exports["sort-sorted"] = a => function(x,v) { if (x.length < 1) { return v["[]"](); } else { return v["_∷_"](x[0], x.slice(1)); } }(
    a,
    {
      "[]": () => exports["Sorted"]["[]"],
      "_∷_": (b,c) => exports["insert-sorted"](b)(exports["sort"](c))(exports["sort-sorted"](c))
  } );
exports["showList"] = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; };
exports["putStrLn"] = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; };
exports["main"] = exports["putStrLn"](
    exports["showList"](
      exports["sort"](
        z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("3"))(
          z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("1"))(
            z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("4"))(
              z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("1"))(
                z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("5"))(
                  z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("9"))(
                    z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("2"))(
                      z_jAgda_Agda_Builtin_List["List"]["_∷_"](agdaRTS.primIntegerFromString("6"))(
                        z_jAgda_Agda_Builtin_List["List"]["[]"]
) ) ) ) ) ) ) ) ) ) );
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

**Generated JS — user code only** (from `insertionsort`, 12,317 bytes total, 1,477 shown; runtime prelude elided):

```js
function InsertionSort_sort($0) {
 switch($0.h) {
  case 0: /* nil */ return {h: 0};
  case undefined: /* cons */ return InsertionSort_insert($0.a1, InsertionSort_sort($0.a2));
 }
}

function InsertionSort_main($0) {
 return Prelude_IO_prim__putStr((Prelude_Show_show_Show_x28Listx20x24ax29({a1: x => Prelude_Show_show_Show_Nat(x), a2: d => x => Prelude_Show_showPrec_Show_Nat(d, x)}, InsertionSort_sort({a1: 3n, a2: {a1: 1n, a2: {a1: 4n, a2: {a1: 1n, a2: {a1: 5n, a2: {a1: 9n, a2: {a1: 2n, a2: {a1: 6n, a2: {h: 0}}}}}}}}}))+'\n'), $0);
}

function InsertionSort_insert($0, $1) {
 switch($1.h) {
  case 0: /* nil */ return {a1: $0, a2: {h: 0}};
  case undefined: /* cons */ {
   const $5 = InsertionSort_comparex27($0, $1.a1);
   switch($5.h) {
    case 0: /* Le */ return {a1: $0, a2: {a1: $1.a1, a2: $1.a2}};
    case 1: /* Gt */ return {a1: $1.a1, a2: InsertionSort_insert($0, $1.a2)};
   }
  }
 }
}

function InsertionSort_comparex27($0, $1) {
 switch($0) {
  case 0n: return {h: 0 /* Le */, a1: 0n};
  default: {
   const $4 = ($0-1n);
   switch($1) {
    case 0n: return {h: 1 /* Gt */, a1: 0n};
    default: {
     const $9 = ($1-1n);
     const $c = InsertionSort_comparex27($4, $9);
     switch($c.h) {
      case 0: /* Le */ return {h: 0 /* Le */, a1: ($c.a1+1n)};
      case 1: /* Gt */ return {h: 1 /* Gt */, a1: ($c.a1+1n)};
     }
    }
   }
  }
 }
}
try{__mainExpression_0()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }
```

**SES probes:**

- `lockdown() + require()`: **pass** (exit 0)
- `Compartment.evaluate()`: **pass** (exit 0)
