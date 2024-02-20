let my_if c a b = if c then a else b;;

my_if true (print_endline "hello") (print_endline "bye");;

let my_if2 c a b = if c then a() else b();;

my_if2 true (fun _ -> print_endline "hello") (fun _ -> print_endline "bye");;

