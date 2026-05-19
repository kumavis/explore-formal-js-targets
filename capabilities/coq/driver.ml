(* Driver exercising both capability patterns. *)

(* The host's predicate: log each call, then test. The "log" is a plain
   side-effecting print; the verified validator doesn't know about it. *)
let logged_pred upper x =
  Printf.printf "  [host log] check %d\n" x;
  x < upper

let () =
  (* === Direction 2: hold a vended counter ================================ *)
  let c = Caps.new_counter () in
  let a = Caps.bump c in
  let b = Caps.bump c in
  let d = Caps.bump c in
  let r = Caps.read c in
  Printf.printf "[vend]    counter Bump x3 → %d,%d,%d ; Read = %d\n" a b d r;

  (* === Direction 1: pass a host-supplied predicate ====================== *)
  let xs = [10; 20; 30; 40] in
  let ok1 = Caps.validate (logged_pred 100) xs in
  Printf.printf "[consume] validate (<100) [10,20,30,40] = %b\n" ok1;
  let ok2 = Caps.validate (logged_pred 30)  xs in
  Printf.printf "[consume] validate (<30)  [10,20,30,40] = %b\n" ok2
