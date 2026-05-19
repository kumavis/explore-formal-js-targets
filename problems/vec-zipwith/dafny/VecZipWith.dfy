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
