type int_fun_sum =
  | Int of int
  | Fun of (int -> int)
;;

let f =
  fun a -> match a with
           | Int y -> y+1
           | Fun g -> g 35 in
let h = fun x -> x + 7 in
f (Fun h)
;;

let rec evenodd = (
    (fun n -> if n == 0 then true  else ((snd evenodd) (n - 1))),
    (fun n -> if n == 0 then false else ((fst evenodd) (n - 1)))
  );;

(fst evenodd) 3;;

let factorial =
    let r = ref (fun n -> n + 1) in
    let f = (fun n -> if n == 0 then 1 else n * ((!r) (n - 1))) in
    r := f;
    f
;;

(factorial 6);;
