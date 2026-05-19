(* Tiny OCaml driver that calls the Coq-extracted `fact` and prints
   the result to stdout. ExtrOcamlNatInt maps Coq's nat to OCaml int. *)

let () =
  let n = 5 in
  let r = Factorial.fact n in
  Printf.printf "factorial(%d) = %d\n" n r
