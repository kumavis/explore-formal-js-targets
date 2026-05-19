let () =
  let n = 10 in
  let s = Sumformula.sum n in
  Printf.printf "sum(0..%d) = %d  (2*sum = %d, n*(n+1) = %d)\n"
    n s (2 * s) (n * (n + 1))
