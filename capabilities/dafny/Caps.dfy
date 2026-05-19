// Two capability patterns in Dafny:
//
// 1. CONSUMING a host-provided capability — `ValidateAll` takes a predicate
//    of Dafny function type `(int) -> bool`. The host (JS) supplies any JS
//    function with matching signature, and Dafny calls it inside a verified
//    loop. The postcondition is stated *in terms of* the opaque predicate.
//
// 2. VENDING a capability — `Counter` is a verified class with monotonic
//    `count` and `Bump()` / `Read()` methods. `MakeCounter()` returns a
//    fresh instance. The class compiles to a JS class the host can hold a
//    reference to and call methods on.

module Caps {

  // --- Consume: validate a sequence against a host-supplied predicate -------

  method ValidateAll(check: int -> bool, xs: seq<int>) returns (ok: bool)
    ensures ok <==> forall i :: 0 <= i < |xs| ==> check(xs[i])
  {
    ok := true;
    var i := 0;
    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant ok <==> forall k :: 0 <= k < i ==> check(xs[k])
    {
      if !check(xs[i]) {
        ok := false;
      }
      i := i + 1;
    }
  }

  // --- Vend: a verified Counter the host can hold and call ------------------

  class Counter {
    var count: nat

    constructor()
      ensures count == 0
    { count := 0; }

    method Bump() returns (r: nat)
      modifies this
      ensures count == old(count) + 1
      ensures r == count
    {
      count := count + 1;
      r := count;
    }

    method Read() returns (r: nat)
      ensures r == count
    { r := count; }
  }

  method MakeCounter() returns (c: Counter)
    ensures fresh(c)
    ensures c.count == 0
  {
    c := new Counter();
  }

  // --- A trivial main so `dafny build` produces a runnable output -----------

  method Main() {
    var xs := [10, 20, 30, 40];
    var allSmall := ValidateAll((x: int) => x < 100, xs);
    print "all < 100? ", allSmall, "\n";

    var c := MakeCounter();
    var a := c.Bump();
    var b := c.Bump();
    var d := c.Bump();
    var r := c.Read();
    print "bump x3 then read = ", r, " (saw ", a, ",", b, ",", d, ")\n";
  }
}
