# Dafny capabilities

Two patterns in one file ([`Caps.dfy`](./Caps.dfy)) and one driver
([`driver.mjs`](./driver.mjs)). Run:

```
nix shell nixpkgs#dafny --command dafny build --target:js Caps.dfy
node driver.mjs
```

Expected output:

```
[consume]    ValidateAll(even, [2,4,6,8]) = true
[consume]    ValidateAll(even, [2,3,6,8]) = false
[vend] Counter bump x3 → seen 1 2 3 ; Read = 3
```

## Consuming a host capability

```dafny
method ValidateAll(check: int -> bool, xs: seq<int>) returns (ok: bool)
  ensures ok <==> forall i :: 0 <= i < |xs| ==> check(xs[i])
```

The `check: int -> bool` parameter has Dafny *function type* — purely
mathematical (Dafny treats it as a total, pure function). At the JS
boundary it's just a JS function `(BigNumber) => boolean`. The host
supplies the predicate and Dafny calls it inside a verified loop:

```js
const hostPredicate = (x) => x.toNumber() % 2 === 0;
const ok = globalThis.Caps.__default.ValidateAll(hostPredicate, xs);
```

Postconditions can mention `check` directly — verification reasons about
the *opaque* function value. That's enough for shape properties
("`ok` is true iff every element passes `check`") but not for properties
that depend on `check`'s behaviour (Dafny has no way to look inside the
JS predicate).

## Vending a verified capability

```dafny
class Counter {
  var count: nat
  constructor() ensures count == 0 { count := 0; }
  method Bump() returns (r: nat)
    modifies this
    ensures count == old(count) + 1
    ensures r == count
  { count := count + 1; r := count; }
  method Read() returns (r: nat) ensures r == count { r := count; }
}
```

`Counter` compiles to a JS class with `Bump()` and `Read()` methods. The
host calls `MakeCounter()` to get a fresh instance, then invokes its
methods directly:

```js
const counter = globalThis.Caps.__default.MakeCounter();
const a = counter.Bump();   // returns BigNumber(1)
const b = counter.Bump();   // returns BigNumber(2)
```

The class's invariants — *every* `Bump` increments `count` by exactly one,
`Read` always reflects the current value — are checked by Dafny at
compile time. The only way for the host to violate them is to swap the
class wholesale or reach into the field directly (which JS *can* do
through `counter.count` since Dafny doesn't emit any private-field
ceremony). Inside SES, freezing the instance with `harden(counter)` is
the natural follow-up.

## Modularization story

This is where Dafny's JS backend fights you. The file looks like:

```js
let _dafny      = (function() { … })();
let _System     = (function() { … })();
let Caps        = (function() { … })();
let _module     = (function() { … })();
_dafny.HandleHaltExceptions(() => Caps.__default.Main(…));
```

Three friction points:

1. **No `module.exports`.** Top-level declarations are module-scoped
   `let`s. `require('./Caps.js')` runs the file but returns `{}`. The
   driver works around this by reading the file as text, rewriting
   `let X =` to `globalThis.X =`, stripping the trailing `Main`
   invocation, and `eval`-ing.

2. **`bignumber.js` dependency.** Dafny's `nat` is a `BigNumber`, not a
   JS `BigInt`. Every integer crossing the boundary needs `.toNumber()`
   or `new BigNumber(n)`. Inside SES this also means endowing `Math`
   because `bignumber.js` calls `Math.random()` at init time — see the
   main repo's `EVALUATION.md` for the gory details.

3. **`Seq<int>` is its own class.** To call `ValidateAll` from JS the
   second argument has to be a `_dafny.Seq.of(BigNumber, BigNumber, …)`,
   not a plain JS array.

A real Dafny→JS integration would either (a) ship the
`generator/bundle.mjs`-style preprocessing as a packaging step, or (b)
upstream a `dafny build --target:js --library` mode that emits proper
ES modules with `BigInt`-typed `nat`. The latter would close most of
the gap with Idris2's FFI ergonomics in one stroke.

## What the verification buys you

Even with the boundary friction, the Counter example is a meaningful
demonstration of *verified* capability vending. A reviewer reading
`Caps.dfy` can see — and Dafny has *checked* — that:

- `Bump` always increments `count` by exactly 1
- `Read` never mutates and always returns the current `count`
- `MakeCounter` always returns a fresh, zeroed instance

Compare with hand-written JS, where the author could promise these
properties in a comment but a malicious or buggy edit can quietly break
them. In a SES tenant that hands a Counter to an untrusted plugin, the
verified invariants are part of the contract — the plugin can't observe
"Bump returned 2 even though my own bump count was 1".
