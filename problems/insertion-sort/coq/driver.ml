let () =
  let xs = [3; 1; 4; 1; 5; 9; 2; 6] in
  let ys = Insertionsort.sort xs in
  Printf.printf "sort([3,1,4,1,5,9,2,6]) = [%s]\n"
    (String.concat ", " (List.map string_of_int ys))
