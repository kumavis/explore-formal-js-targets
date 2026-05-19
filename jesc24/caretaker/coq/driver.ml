let show_opt = function
  | None   -> "nothing"
  | Some n -> "just " ^ string_of_int n

let () =
  let c = Caretaker.make_caretaker (fun n -> n * 2) in

  let r0 = Caretaker.wrap c 10 in
  Printf.printf "default (disabled): wrap 10 = %s\n" (show_opt r0);

  Caretaker.enable c;
  let r1 = Caretaker.wrap c 10 in
  Printf.printf "enabled:            wrap 10 = %s\n" (show_opt r1);
  let r2 = Caretaker.wrap c 7  in
  Printf.printf "enabled:            wrap 7  = %s\n" (show_opt r2);

  Caretaker.disable c;
  let r3 = Caretaker.wrap c 10 in
  Printf.printf "disabled:           wrap 10 = %s\n" (show_opt r3)
