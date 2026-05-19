# List reverse (with reverse-reverse-identity proof)

Naive list reverse with the theorem reverse(reverse(xs)) ≡ xs. Dafny proves it with SMT and a couple of induction lemmas; Agda and Idris2 prove it with structural induction and rewrite tactics.

## Summary

| Language | Source LOC | Source bytes | Compiled JS (solution + library = total) | Output | Status |
| --- | ---: | ---: | ---: | --- | --- |
| Dafny | 38 | 792 | 1,375 + 30,836 = 32,211 | `reverse([1,2,3,4]) = [4, 3, 2, 1]` | ✅ ok |
| Agda | 60 | 2,178 | 1,904 + 14,926 = 16,830 | `[4,3,2,1]` | ✅ ok |
| Idris2 | 34 | 1,160 | 612 + 11,238 = 11,850 | `[4, 3, 2, 1]` | ✅ ok |
| Coq | 34 | 896 | 1,658 + 69,581 = 71,239 | `reverse([1,2,3,4]) = [4, 3, 2, 1]` | ✅ ok |

## SES compatibility

| Language | Needs bundling | Static scan | `lockdown()` + `require()` | Raw `Compartment.evaluate()` | Bundled (`@endo/bundle-source` → `importBundle`) | Compartment endowments |
| --- | :---: | :---: | :---: | :---: | :---: | --- |
| Dafny | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass | `console` + `BigNumber` + `Math` |
| Agda | **yes** | ✅ clean | ✅ pass | ❌ evaluate-failed | ✅ pass | `console` |
| Idris2 | no | ✅ clean | ✅ pass | ✅ pass | ✅ pass | `console` |
| Coq | no | ✅ clean | ✅ pass | ❌ evaluate-failed | ❌ import-failed | `console` + `TextDecoder` + `TextEncoder` + `Int8Array` + `Uint8Array` + `Uint8ClampedArray` + `Int16Array` + `Uint16Array` + `Int32Array` + `Uint32Array` + `Float32Array` + `Float64Array` + `BigInt64Array` + `BigUint64Array` + `ArrayBuffer` + `DataView` |

> **Dafny bundling requirement:** the bundled compartment passes only with `Math` (in addition to `BigNumber`) endowed. Dafny's emitted runtime calls `bignumber.js`, which invokes `Math.random()` during initialization — SES's secure-mode `Math` removes `random`, so without the endowment the bundle imports fail at load. A real deployment should wrap `Math` rather than passing the host's.

> **Coq bundling requirement:** js_of_ocaml's runtime reaches for `TextDecoder`/`TextEncoder` and the full set of typed-array constructors (`Float32Array`, `Int32Array`, `ArrayBuffer`, `DataView`, …); SES Compartments don't expose those by default, so they must be endowed. Even with those endowed, the bundle still fails import — see the Coq footnote below.

> **Coq Compartment failure:** js_of_ocaml's runtime mutates host globals during initialization (e.g. assigning `jsoo_create_file` onto a top-level object). SES `lockdown()` freezes every standard intrinsic, so the assignment throws `Cannot add property …, object is not extensible`. This is a fundamental incompatibility: even with comprehensive endowments, the bundle does not import into a sealed Compartment without either (a) patching the js_of_ocaml runtime to skip global mutation, or (b) relaxing SES (`overrideTaming: 'min'` and friends), neither of which is in scope here.

> **Coq raw `Compartment.evaluate()` failure:** the same SES-vs-js_of_ocaml mismatch shows up earlier here than in the bundled case — the runtime asks for `TextDecoder` before anything else and the default Compartment doesn't expose it. See the "Coq bundling requirement" note above for the deeper story.

### Bundle details

| Language | Bundle bytes (base64) | Imported keys | Notes |
| --- | ---: | --- | --- |
| Dafny | 162,760 | _dafny, _System, Reverse, _module, default | imported keys: _dafny, _System, Reverse, _module, default |
| Agda | 38,456 | reverse, showList, putStrLn, main, default, _++_ | imported keys: reverse, showList, putStrLn, main, default, _++_ |
| Idris2 | 17,596 | reverse, default | imported keys: reverse, default |
| Coq | 100,080 | — | import error: `Cannot add property jsoo_create_file, object is not extensible` |

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

**Generated JS — user code only** (from `Reverse.js`, 32,211 bytes total, 1,375 shown; runtime prelude elided):

```js
let Reverse = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Reverse._default";
    }
    _parentTraits() {
      return [];
    }
    static Rev(xs) {
      let _0___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_dafny.Seq.of(), _0___accumulator);
        } else {
          _0___accumulator = _dafny.Seq.Concat(_dafny.Seq.of((xs)[_dafny.ZERO]), _0___accumulator);
          let _in0 = (xs).slice(_dafny.ONE);
          xs = _in0;
          continue TAIL_CALL_START;
        }
      }
    };
    static Main(__noArgsParameter) {
      let _0_xs;
      _0_xs = _dafny.Seq.of(_dafny.ONE, new BigNumber(2), new BigNumber(3), new BigNumber(4));
      let _1_ys;
      _1_ys = Reverse.__default.Rev(_0_xs);
      process.stdout.write((_dafny.Seq.UnicodeFromString("reverse([1,2,3,4]) = ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(_1_ys));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
  };
  return $module;
})(); // end of module Reverse

// ... runtime prelude elided ...

_dafny.HandleHaltExceptions(() => Reverse.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
```

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

**Generated JS — user code only** (from `jAgda.Reverse.js`, 1,932 bytes total, 1,904 shown; runtime prelude elided):

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
```

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

**Generated JS — user code only** (from `reverse`, 11,850 bytes total, 612 shown; runtime prelude elided):

```js
function Reverse_myReverse($0) {
 switch($0.h) {
  case 0: /* nil */ return {h: 0};
  case undefined: /* cons */ return Prelude_Types_List_tailRecAppend(Reverse_myReverse($0.a2), {a1: $0.a1, a2: {h: 0}});
 }
}

function Reverse_main($0) {
 return Prelude_IO_prim__putStr((Prelude_Show_show_Show_x28Listx20x24ax29({a1: x => Prelude_Show_show_Show_Int(x), a2: d => x => Prelude_Show_showPrec_Show_Int(d, x)}, Reverse_myReverse({a1: 1, a2: {a1: 2, a2: {a1: 3, a2: {a1: 4, a2: {h: 0}}}}}))+'\n'), $0);
}
try{__mainExpression_0()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }
```

---

## Coq

**Source** (`problems/reverse/coq/Reverse.v`):

```coq
(* List reverse with the involution proof, and extraction to OCaml. *)

Require Import Coq.Lists.List.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Import ListNotations.

Fixpoint myrev {A : Type} (xs : list A) : list A :=
  match xs with
  | []      => []
  | x :: xs' => myrev xs' ++ [x]
  end.

Lemma myrev_app : forall (A : Type) (xs ys : list A),
  myrev (xs ++ ys) = myrev ys ++ myrev xs.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Theorem myrev_involutive : forall (A : Type) (xs : list A),
  myrev (myrev xs) = xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite myrev_app. simpl. rewrite IH. reflexivity.
Qed.

Extraction Language OCaml.
Extraction "reverse.ml" myrev.

```

**Build:** exit `0`

**Run:** exit `0` — stdout: `reverse([1,2,3,4]) = [4, 3, 2, 1]`

**Generated JS — user code only** (from `reverse.js`, 71,239 bytes total, 1,658 shown; runtime prelude elided):

```js
// (js_of_ocaml bundles the entire OCaml runtime + extracted user
//  code into a single closure with mangled identifiers; symbol-
//  based extraction is not feasible. Showing the bundle tail —
//  the verified `fact` is the recursive `function bM(a){ … }`
//  near the end.)
//
// …
1:var
f=c[2],g=c[1];if(0===f[0]){var
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
l=c[2];T(a,c[1]);ed(a,l);return}}}function
bM(a,b){if(!a)return b;var
c=bM(a[2],b);return[0,a[1],c]}function
bN(a){if(!a)return a;var
b=[0,a[1],0];return bM(bN(a[2]),b)}var
dx=function(a,b){if(!b)return e;if(!b[2])return b[1];var
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
e[d+1]=0;return[0,o,i]}}(function(a){return e+a},bN([0,1,[0,2,[0,3,[0,4,0]]]])));D(i(function(a){T(c6,a);return 0},0,[0,[11,"reverse([1,2,3,4]) = [",[2,0,[11,"]\n",0]]],"reverse([1,2,3,4]) = [%s]\n"][1]),dx);bH(0);return}(globalThis));

```
