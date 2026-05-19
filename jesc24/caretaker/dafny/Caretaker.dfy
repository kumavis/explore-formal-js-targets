// Revocable caretaker, after agoric-labs/jesc24's
// `theories/heap_lang/lib/caretaker.v`.
//
// Two verified entry points coexist:
//   `Wrap`    — has precondition `requires enabled`, so a *caller* who
//               cannot prove the caretaker is currently enabled cannot
//               even call it. This is the compile-time revocation
//               guarantee.
//   `TryWrap` — returns `(ok, r)`; runtime-checks the flag. Used for
//               demonstrations where we want to actually *observe* the
//               revoked behaviour rather than have the verifier
//               reject the call.

module Caretaking {

  class Caretaker {
    var enabled: bool
    const f: int -> int

    constructor(target: int -> int)
      ensures !enabled
      ensures f == target
    { enabled := false; f := target; }

    method Wrap(v: int) returns (r: int)
      requires enabled
      ensures r == f(v)
    { r := f(v); }

    method TryWrap(v: int) returns (ok: bool, r: int)
      ensures ok == enabled
      ensures ok ==> r == f(v)
    {
      if enabled { ok := true;  r := f(v); }
      else       { ok := false; r := 0; }
    }

    method Enable()  modifies this ensures enabled  { enabled := true;  }
    method Disable() modifies this ensures !enabled { enabled := false; }
  }

  method Main() {
    var c := new Caretaker(v => v * 2);

    var ok0, r0 := c.TryWrap(10);
    print "default (disabled): wrap 10 = ok=", ok0, " r=", r0, "\n";

    c.Enable();
    var ok1, r1 := c.TryWrap(10);
    print "enabled:            wrap 10 = ok=", ok1, " r=", r1, "\n";
    var ok2, r2 := c.TryWrap(7);
    print "enabled:            wrap 7  = ok=", ok2, " r=", r2, "\n";

    c.Disable();
    var ok3, r3 := c.TryWrap(10);
    print "disabled:           wrap 10 = ok=", ok3, " r=", r3, "\n";
  }
}
