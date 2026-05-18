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
