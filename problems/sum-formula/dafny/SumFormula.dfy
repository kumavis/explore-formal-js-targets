// Triangular-number closed form: 2 * sum(0..n) == n * (n + 1).
//
// Dafny dispatches both the recursive definition and the inductive proof
// in a handful of lines because the SMT backend handles the nonlinear
// arithmetic step (`2 * (n + sum(n-1)) == n*n + n` after unfolding the IH).

module SumFormula {

  function Sum(n: nat): nat {
    if n == 0 then 0 else n + Sum(n - 1)
  }

  // The whole closed-form theorem: one induction, SMT does the algebra.
  lemma ClosedForm(n: nat)
    ensures 2 * Sum(n) == n * (n + 1)
  {
    if n == 0 {
    } else {
      ClosedForm(n - 1);
    }
  }

  method Main() {
    var n := 10;
    var s := Sum(n);
    print "sum(0..10) = ", s, "  (2*sum = ", 2 * s, ", n*(n+1) = ", n * (n + 1), ")\n";
  }
}
