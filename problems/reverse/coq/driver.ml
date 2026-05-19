let () =
  let xs = [1; 2; 3; 4] in
  let ys = Reverse.myrev xs in
  Printf.printf "reverse([1,2,3,4]) = [%s]\n"
    (String.concat ", " (List.map string_of_int ys))
