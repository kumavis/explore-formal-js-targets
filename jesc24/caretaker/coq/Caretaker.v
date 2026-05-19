(* Revocable caretaker, after agoric-labs/jesc24's
   `theories/heap_lang/lib/caretaker.v`.

   Coq has no native mutable state; the caretaker's enabled flag and
   wrapped function are bound to OCaml-side `bool ref`s via
   `Extract Constant`. The typed interface (`Caretaker`, `wrap`,
   `enable`, `disable`) is what Coq enforces; the body lives in
   OCaml. *)

Require Import Coq.Init.Datatypes.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Parameter Caretaker      : Type.
Parameter make_caretaker : (nat -> nat) -> Caretaker.
Parameter wrap           : Caretaker -> nat -> option nat.
Parameter enable         : Caretaker -> unit.
Parameter disable        : Caretaker -> unit.

(* OCaml realisation. *)
Extract Constant Caretaker      => "{ mutable on : bool; f : int -> int }".
Extract Constant make_caretaker => "(fun f -> { on = false; f })".
Extract Constant wrap           =>
  "(fun c v -> if c.on then Some (c.f v) else None)".
Extract Constant enable         => "(fun c -> c.on <- true)".
Extract Constant disable        => "(fun c -> c.on <- false)".

Extraction Language OCaml.
Extraction "caretaker.ml" make_caretaker wrap enable disable.
