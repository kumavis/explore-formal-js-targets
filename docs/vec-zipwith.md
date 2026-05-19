# Vec.zipWith (length-indexed vectors)

A showcase for **dependent types**: `zipWith` on a length-indexed `Vec n A` has no "lengths don't match" case to handle — Agda and Idris2 eliminate that possibility at compile time. Dafny has no equivalent (no type-level `Nat` indices), so it expresses the same guarantee as a runtime precondition `requires |xs| == |ys|`.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 28 | 906 | 1,749 + 30,839 = 32,588 | `zipWith(+, [1,2,3], [10,20,30]) = [11, 22, 33]` | ✅ ok |
| Agda | 52 | 1,780 | 2,052 + 14,759 = 16,811 | `[11,22,33]` | ✅ ok |
| Idris2 | 33 | 1,009 | 605 + 11,014 = 11,619 | `[11, 22, 33]` | ✅ ok |

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
| Dafny | 163,300 | _dafny, _System, VecZipWith, _module, default | imported keys: _dafny, _System, VecZipWith, _module, default |
| Agda | 37,588 | Vec, zipWith, vecToList, xs, ys, result, showList, putStrLn, main, default | imported keys: Vec, zipWith, vecToList, xs, ys, result, showList, putStrLn, main, default |
| Idris2 | 17,284 | zipWith, default | imported keys: zipWith, default |

---

## Dafny

**Source** (`problems/vec-zipwith/dafny/VecZipWith.dfy`):

```dafny
// zipWith on plain sequences.
//
// Note the asymmetry with the Agda/Idris2 versions: Dafny's sequences
// don't carry length in the type, so we have to express "same length"
// as a runtime precondition every caller is obligated to discharge.
// The compile-time guarantee from dependent types becomes a runtime
// contract — same correctness, more verification per call site.

module VecZipWith {

  function ZipWith(f: (int, int) -> int, xs: seq<int>, ys: seq<int>): (r: seq<int>)
    requires |xs| == |ys|
    ensures |r| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> r[i] == f(xs[i], ys[i])
  {
    if |xs| == 0 then []
    else [f(xs[0], ys[0])] + ZipWith(f, xs[1..], ys[1..])
  }

  method Main() {
    var xs := [1, 2, 3];
    var ys := [10, 20, 30];
    var add := (a: int, b: int) => a + b;
    var r := ZipWith(add, xs, ys);
    print "zipWith(+, [1,2,3], [10,20,30]) = ", r, "\n";
  }
}

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `zipWith(+, [1,2,3], [10,20,30]) = [11, 22, 33]`

**Generated JS — user code only** (from `VecZipWith.js`, 32,588 bytes total, 1,749 shown; runtime prelude elided):

```js
let VecZipWith = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "VecZipWith._default";
    }
    _parentTraits() {
      return [];
    }
    static ZipWith(f, xs, ys) {
      let _0___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_0___accumulator, _dafny.Seq.of());
        } else {
          _0___accumulator = _dafny.Seq.Concat(_0___accumulator, _dafny.Seq.of((f)((xs)[_dafny.ZERO], (ys)[_dafny.ZERO])));
          let _in0 = f;
          let _in1 = (xs).slice(_dafny.ONE);
          let _in2 = (ys).slice(_dafny.ONE);
          f = _in0;
          xs = _in1;
          ys = _in2;
          continue TAIL_CALL_START;
        }
      }
    };
    static Main(__noArgsParameter) {
      let _0_xs;
      _0_xs = _dafny.Seq.of(_dafny.ONE, new BigNumber(2), new BigNumber(3));
      let _1_ys;
      _1_ys = _dafny.Seq.of(new BigNumber(10), new BigNumber(20), new BigNumber(30));
      let _2_add;
      _2_add = function (_3_a, _4_b) {
        return (_3_a).plus(_4_b);
      };
      let _5_r;
      _5_r = VecZipWith.__default.ZipWith(_2_add, _0_xs, _1_ys);
      process.stdout.write((_dafny.Seq.UnicodeFromString("zipWith(+, [1,2,3], [10,20,30]) = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(_5_r));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
  };
  return $module;
})(); // end of module VecZipWith

// ... runtime prelude elided ...

_dafny.HandleHaltExceptions(() => VecZipWith.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
```

---

## Agda

**Source** (`problems/vec-zipwith/agda/VecZipWith.agda`):

```agda
-- Length-indexed vectors and zipWith.
-- The type `Vec A n` carries the length as a type-level Nat, so the
-- zipWith function has no "lengths don't match" case to handle — the
-- type system has already eliminated that possibility.

module VecZipWith where

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat -> Set where
  []  : Vec A 0
  _∷_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 5 _∷_

-- Note the type: both inputs and the output share the same length n.
-- The four-case pattern match is exhaustive precisely because Vec's
-- indices rule out the (cons, nil) and (nil, cons) cases.
zipWith : {A B C : Set} {n : Nat} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWith f []       []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

-- A few small sample vectors and the result of zipWith (+).
xs : Vec Nat 3
xs = 1 ∷ 2 ∷ 3 ∷ []

ys : Vec Nat 3
ys = 10 ∷ 20 ∷ 30 ∷ []

result : Vec Nat 3
result = zipWith (\ a b -> a + b) xs ys

-- Executable entry point.  We import List qualified as `L` so its `_∷_`
-- doesn't fight with the Vec `_∷_` constructor.
open import Agda.Builtin.List as L using (List)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

vecToList : {A : Set} {n : Nat} -> Vec A n -> List A
vecToList []       = L.[]
vecToList (x ∷ xs) = x L.∷ vecToList xs

postulate
  showList : List Nat -> String
  putStrLn : String -> IO ⊤
{-# COMPILE JS showList = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; } #-}
{-# COMPILE JS putStrLn = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (showList (vecToList result))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `[11,22,33]`

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

**Generated JS — user code only** (from `jAgda.VecZipWith.js`, 2,080 bytes total, 2,052 shown; runtime prelude elided):

```js
var agdaRTS = require("agda-rts");

var z_jAgda_Agda_Builtin_IO = require("jAgda.Agda.Builtin.IO");
var z_jAgda_Agda_Builtin_List = require("jAgda.Agda.Builtin.List");
var z_jAgda_Agda_Builtin_Nat = require("jAgda.Agda.Builtin.Nat");
var z_jAgda_Agda_Builtin_String = require("jAgda.Agda.Builtin.String");
var z_jAgda_Agda_Builtin_Unit = require("jAgda.Agda.Builtin.Unit");
var z_jAgda_Agda_Primitive = require("jAgda.Agda.Primitive");

exports["Vec"] = {};
exports["Vec"]["[]"] = a => a["[]"]();
exports["Vec"]["_∷_"] = a => b => c => d => d["_∷_"](a,b,c);
exports["zipWith"] = a => b => c => d => e => f => g => f({
    "[]": () => agdaRTS.primSeq(g,f),
    "_∷_": (h,i,j) => g({
      "_∷_": (k,l,m) => exports["Vec"]["_∷_"](null)(e(i)(l))(
        exports["zipWith"](null)(null)(null)(null)(e)(j)(m)
      )
    })
  });
exports["vecToList"] = a => b => c => c({
    "[]": () => z_jAgda_Agda_Builtin_List["List"]["[]"],
    "_∷_": (d,e,f) => z_jAgda_Agda_Builtin_List["List"]["_∷_"](e)(exports["vecToList"](null)(null)(f))
  });
exports["xs"] = exports["Vec"]["_∷_"](null)(agdaRTS.primIntegerFromString("1"))(
    exports["Vec"]["_∷_"](null)(agdaRTS.primIntegerFromString("2"))(
      exports["Vec"]["_∷_"](null)(agdaRTS.primIntegerFromString("3"))(exports["Vec"]["[]"])
  ) );
exports["ys"] = exports["Vec"]["_∷_"](null)(agdaRTS.primIntegerFromString("10"))(
    exports["Vec"]["_∷_"](null)(agdaRTS.primIntegerFromString("20"))(
      exports["Vec"]["_∷_"](null)(agdaRTS.primIntegerFromString("30"))(exports["Vec"]["[]"])
  ) );
exports["result"] = exports["zipWith"](null)(null)(null)(null)(
      a => b => agdaRTS.uprimIntegerPlus(a,b)
  )(exports["xs"])(exports["ys"]);
exports["showList"] = function (xs) { return "[" + xs.map(function (x) { return x.toString(); }).join(",") + "]"; };
exports["putStrLn"] = function (s) { return function(cb) { process.stdout.write(s + "\n"); cb(0); }; };
exports["main"] = exports["putStrLn"](
    exports["showList"](
      exports["vecToList"](null)(null)(exports["result"])
) );
```

---

## Idris2

**Source** (`problems/vec-zipwith/idris2/VecZipWith.idr`):

```idris
||| Length-indexed vectors and zipWith.
||| The type `Vec n A` carries the length as a type-level Nat, so the
||| zipWith function has no "lengths don't match" case to handle — the
||| type system has already eliminated that possibility.

module VecZipWith

%default total

data Vec : Nat -> Type -> Type where
  VNil  : Vec Z a
  VCons : a -> Vec n a -> Vec (S n) a

-- Both inputs and the output share the same length n.
-- The two-case pattern match is exhaustive precisely because Vec's
-- index rules out the (cons, nil) / (nil, cons) cases.
zipWith : (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f VNil          VNil          = VNil
zipWith f (VCons x xs) (VCons y ys)   = VCons (f x y) (zipWith f xs ys)

vecToList : Vec n a -> List a
vecToList VNil          = []
vecToList (VCons x xs) = x :: vecToList xs

xs : Vec 3 Nat
xs = VCons 1 (VCons 2 (VCons 3 VNil))

ys : Vec 3 Nat
ys = VCons 10 (VCons 20 (VCons 30 VNil))

main : IO ()
main = printLn (vecToList (VecZipWith.zipWith (+) xs ys))

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `[11, 22, 33]`

**Generated JS — user code only** (from `veczipwith`, 11,619 bytes total, 605 shown; runtime prelude elided):

```js
function VecZipWith_zipWith($0, $1, $2) {
 switch($1.h) {
  case 0: /* nil */ return {h: 0};
  case undefined: /* cons */ return {a1: $0($1.a1)($2.a1), a2: VecZipWith_zipWith($0, $1.a2, $2.a2)};
 }
}

function VecZipWith_main($0) {
 return Prelude_IO_prim__putStr((Prelude_Show_show_Show_x28Listx20x24ax29({a1: x => Prelude_Show_show_Show_Nat(x), a2: d => x => Prelude_Show_showPrec_Show_Nat(d, x)}, VecZipWith_zipWith($10 => $11 => ($10+$11), VecZipWith_xs(), VecZipWith_ys()))+'\n'), $0);
}
try{__mainExpression_0()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }
```
