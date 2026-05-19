let () =
  let xs = [1; 2; 3] in
  let ys = [10; 20; 30] in
  let zs = Veczipwith.zipWith (+) xs ys in
  Printf.printf "zipWith(+, [1,2,3], [10,20,30]) = [%s]\n"
    (String.concat ", " (List.map string_of_int zs))
