# Vec.zipWith (length-indexed vectors)

A showcase for **dependent types**: `zipWith` on a length-indexed `Vec n A` has no "lengths don't match" case to handle — Agda and Idris2 eliminate that possibility at compile time. Dafny has no equivalent (no type-level `Nat` indices), so it expresses the same guarantee as a runtime precondition `requires |xs| == |ys|`.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 28 | 906 | 1,749 + 30,839 = 32,588 | `zipWith(+, [1,2,3], [10,20,30]) = [11, 22, 33]` | ✅ ok |
| Agda | 52 | 1,780 | 2,052 + 14,759 = 16,811 | `[11,22,33]` | ✅ ok |
| Idris2 | 33 | 1,009 | 605 + 11,014 = 11,619 | `[11, 22, 33]` | ✅ ok |
| Coq | 48 | 1,933 | 1,666 + 69,618 = 71,284 | `zipWith(+, [1,2,3], [10,20,30]) = [11, 22, 33]` | ✅ ok |

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
| Dafny | 163,300 | _dafny, _System, VecZipWith, _module, default | imported keys: _dafny, _System, VecZipWith, _module, default |
| Agda | 37,588 | Vec, zipWith, vecToList, xs, ys, result, showList, putStrLn, main, default | imported keys: Vec, zipWith, vecToList, xs, ys, result, showList, putStrLn, main, default |
| Idris2 | 17,284 | zipWith, default | imported keys: zipWith, default |
| Coq | 100,172 | — | import error: `Cannot add property jsoo_create_file, object is not extensible` |

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

---

## Coq

**Source** (`problems/vec-zipwith/coq/VecZipWith.v`):

```coq
(* Coq has length-indexed vectors via Coq.Vectors.Vector, but extracting
   them through OCaml is brittle (the GADT-style encoding produces awkward
   Obj.magic dances). So this port follows the Dafny shape: zipWith on
   plain lists with a length-match runtime precondition.

   This is honest about Coq's position: it CAN express the length-indexed
   guarantee at the source level — see the comment block at the bottom —
   but the OCaml back end does not produce idiomatic JS from it. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Import ListNotations.

Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xs', y :: ys' => f x y :: zipWith f xs' ys'
  | _, _ => []
  end.

(* Verified property: if the inputs have the same length, the result has
   that length and each position holds the pointwise f of the inputs. *)
Lemma zipWith_length : forall A B C (f : A -> B -> C) xs ys,
  length xs = length ys -> length (zipWith f xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] Hlen; simpl; try discriminate.
  - reflexivity.
  - simpl in Hlen. injection Hlen as Hlen. rewrite (IH ys Hlen). reflexivity.
Qed.

(* If we'd wanted to forbid mismatched lengths *at the type level* the way
   Agda's Vec does, the source signature would be:

     Definition zipWithVec {A B C n} (f : A -> B -> C)
       (xs : Vector.t A n) (ys : Vector.t B n) : Vector.t C n :=
         Vector.map2 f xs ys.

   The proof obligation disappears (the type checker enforces n = n), but
   the extracted OCaml is not idiomatic and js_of_ocaml's output for
   Vector.t includes Obj.magic noise. The price of expressivity is paid
   at the seam. *)

Extraction Language OCaml.
Extraction "veczipwith.ml" zipWith.

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `zipWith(+, [1,2,3], [10,20,30]) = [11, 22, 33]`

**Generated JS — user code only** (from `veczipwith.js`, 71,284 bytes total, 1,666 shown; runtime prelude elided):

```js
// (js_of_ocaml bundles the entire OCaml runtime + extracted user
//  code into a single closure with mangled identifiers; symbol-
//  based extraction is not feasible. Showing the bundle tail —
//  the verified `fact` is the recursive `function bM(a){ … }`
//  near the end.)
//
// …
i=f[1];T(a,g);aG(a,"@{");c=i}else{var
j=f[1];T(a,g);aG(a,"@[");c=j}break;case
6:var
m=c[2];T(a,c[1]);return D(m,a);case
7:T(a,c[1]);ap(a);return;case
8:var
n=c[2];T(a,c[1]);return at(n);case
2:case
4:var
k=c[2];T(a,c[1]);return aG(a,k);default:var
l=c[2];T(a,c[1]);ec(a,l);return}}}function
bM(a,b,c){if(b)if(c)var
e=bM(a,b[2],c[2]),d=[0,L(a,b[1],c[1]),e];else
var
d=c;else
var
d=b;return d}var
dw=function(a,b){if(!b)return e;if(!b[2])return b[1];var
j=r(a);a:{var
d=0,c=b,p=0;for(;;){if(!c){var
n=d;break a}var
k=c[1];if(!c[2])break;var
l=c[2],m=(r(k)+j|0)+d|0;if(d<=m){d=m;c=l}else{d=at("String.concat");c=l}}var
n=r(k)+d|0}var
i=A(n),h=p,g=b;for(;;){if(g){var
f=g[1];if(g[2]){var
o=g[2];am(f,0,i,h,r(f));am(a,0,i,h+r(f)|0,j);h=(h+r(f)|0)+j|0;g=o;continue}am(f,0,i,h,r(f))}return F(i)}}(bd,function(a,b){if(!b)return 0;var
f=b[2],h=b[1];if(!f)return[0,D(a,h),0];var
m=f[2],n=f[1],o=D(a,h),l=24029,i=[0,D(a,n),l],e=i,d=1,c=m;for(;;){if(c){var
g=c[2],j=c[1];if(g){var
p=g[2],q=g[1],r=D(a,j),k=[0,D(a,q),l];e[d+1]=[0,r,k];e=k;d=1;c=p;continue}e[d+1]=[0,D(a,j),0]}else
e[d+1]=0;return[0,o,i]}}(function(a){return e+a},bM(function(a,b){return a+b|0},[0,1,[0,2,[0,3,0]]],[0,10,[0,20,[0,30,0]]])));D(i(function(a){T(c5,a);return 0},0,[0,[11,"zipWith(+, [1,2,3], [10,20,30]) = [",[2,0,[11,"]\n",0]]],"zipWith(+, [1,2,3], [10,20,30]) = [%s]\n"][1]),dw);bH(0);return}(globalThis));

```
