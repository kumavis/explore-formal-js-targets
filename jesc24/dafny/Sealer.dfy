// Dynamic sealer / unsealer pair, after agoric-labs/jesc24's `sealing.v`.
//
// Dafny gives us two things the Idris2 port doesn't get for free:
//   1. `class Box` — references are unforgeable identities; there's no way
//      for a caller to fabricate a Box that wasn't returned by `Seal`.
//   2. `requires b in tbl` — the OCAP property is verified at compile time.
//      A caller cannot type-check a call to `Unseal` on a Box the verifier
//      can't prove this sealer issued.

module Sealing {

  class Box {
    // empty; only its reference identity matters
  }

  class Sealer {
    var tbl: map<Box, int>

    constructor()
      ensures tbl == map[]
    { tbl := map[]; }

    method Seal(v: int) returns (b: Box)
      modifies this
      ensures fresh(b)
      ensures b in tbl
      ensures tbl[b] == v
      ensures forall k :: k in old(tbl) ==> k in tbl && tbl[k] == old(tbl[k])
    {
      b := new Box;
      tbl := tbl[b := v];
    }

    method Unseal(b: Box) returns (r: int)
      requires b in tbl
      ensures r == tbl[b]
    { r := tbl[b]; }
  }

  // Demonstration. The cross-sealer call is commented because Dafny
  // would *refuse to compile it* — the precondition `b in tbl` does
  // not hold for a Box created by a different Sealer.
  method Main() {
    var s1 := new Sealer();
    var s2 := new Sealer();

    var b := s1.Seal(42);
    var r := s1.Unseal(b);
    print "s1.Unseal(s1.Seal(42)) = ", r, "\n";

    // Uncommenting this is a verification error:
    //   var bad := s2.Unseal(b);
    // because Dafny cannot prove `b in s2.tbl`.
    print "s2.Unseal(s1.Seal(42)) is rejected at verification time.\n";
  }
}
