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
