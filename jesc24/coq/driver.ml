let show_opt = function
  | None -> "None"
  | Some n -> "Some " ^ string_of_int n

let () =
  let s1 = Sealer.make_sealer () in
  let s2 = Sealer.make_sealer () in
  let k = Sealer.seal s1 42 in
  let r1 = Sealer.unseal s1 k in
  Printf.printf "s1.unseal(s1.seal(42)) = %s\n" (show_opt r1);
  let r2 = Sealer.unseal s2 k in
  Printf.printf "s2.unseal(s1.seal(42)) = %s\n" (show_opt r2)
