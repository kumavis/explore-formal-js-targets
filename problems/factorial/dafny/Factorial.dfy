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
