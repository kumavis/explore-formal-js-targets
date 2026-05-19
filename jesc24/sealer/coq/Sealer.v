(* Dynamic sealer / unsealer pair, after agoric-labs/jesc24's `sealing.v`.

   Coq has no native mutable state; we declare the interface as
   Parameters and bind it to OCaml-side definitions via Extract Constant.
   Tokens are OCaml unit-refs (`unit ref`), compared with physical
   equality (`==`) so different sealers' tokens cannot collide.

   The Coq side cannot *prove* anything about the OCaml realisation,
   but the typed interface is enforced at every Coq call site:

     unseal : Sealer -> Token -> option nat

   means callers can't pass a non-Token, and must handle the `None`
   case (token wasn't issued by this sealer). *)

Require Import Coq.Init.Datatypes.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.

Parameter Sealer : Type.
Parameter Token  : Type.
Parameter make_sealer : unit -> Sealer.
Parameter seal   : Sealer -> nat -> Token.
Parameter unseal : Sealer -> Token -> option nat.

(* OCaml realisation: a Sealer is a ref to an assoc list mapping unit-refs
   to ints. Physical equality (`==`) on the refs gives us OCAP-grade
   identity — fresh `ref ()` calls are unforgeable. *)
Extract Constant Sealer       => "(unit ref * int) list ref".
Extract Constant Token        => "unit ref".
Extract Constant make_sealer  => "(fun () -> ref [])".
Extract Constant seal         => "(fun s v -> let k = ref () in s := (k, v) :: !s; k)".
Extract Constant unseal       =>
  "(fun s k ->
      let rec find = function
        | [] -> None
        | (k', v) :: _ when k' == k -> Some v
        | _ :: rest -> find rest
      in find !s)".

Extraction Language OCaml.
Extraction "sealer.ml" make_sealer seal unseal.
