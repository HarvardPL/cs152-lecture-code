(* continuation-passing style
   example adapted from Appel
 *)
let isprime n = true;; (* TODO *)

let rec prodprimes n =
  if n == 1
  then 1
  else if isprime n
  then n * (prodprimes (n-1))
  else (prodprimes (n-1));;

let isprime_cps n c = c true;; (* TODO **)

let rec prodprimes_cps n c =
  if n == 1
  then (c 1)
  else let k = fun b ->
         if b
         then let j = fun p ->
                let a = n*p
                in (c a)
              and m = n-1
              in (prodprimes_cps m j)
         else let h = fun q -> (c q)
              and i = n - 1
              in (prodprimes_cps i h)
       in (isprime_cps n k);;

prodprimes_cps 6 (fun v -> v);;

let rec prodprimes_hcps n c =
  if n == 1
  then (c 1)
  else (isprime_cps n (fun b ->
            if b
            then (prodprimes_hcps (n-1) (fun p -> (c (n*p))))
            else (prodprimes_hcps (n-1) c)));;

prodprimes_hcps 6 (fun v -> v);;

(* other higher-level example *)
(* success continuation *)
(* failure continuation *)

type 'a tree =
  | Leaf of 'a
  | Node of ('a tree * 'a tree);;
           
let rec dfs tree predicate success failure =
  match tree with
  | Leaf elem -> if (predicate elem) then (success elem) else (failure ())
  | Node (left, right) -> dfs left predicate success (fun () -> dfs right predicate success failure);;

exception Not_Found;;

let search tree predicate =
  dfs tree predicate (fun x -> x) (fun () -> raise Not_Found);;

search (Node (Leaf 1, (Node (Leaf 2, Leaf 3)))) (fun n -> n mod 2 == 0);;

(* basic factorial example *)
let rec fact n =
  if n <= 0
  then 1
  else n * (fact (n-1));;

let rec fact_iter n a =
  if n <= 0
  then a
  else (fact_iter (n-1) (n*a));;

let rec fact_cps n k =
  if n <= 0
  then k 1
  else (fact_cps (n-1) (fun r -> k (n*r)));;

(* product example *)

let rec product xs = match xs with
  | [] -> 1
  | x::xs -> x * product xs;;

let rec product_cps xs k = match xs with
  | [] -> k 1
  | x::xs -> product_cps xs (fun r -> k (x * r));;

#trace product_cps;;

product_cps [1;2;0;4;5;6;7;8] (fun v -> v);;

let rec product_cps0 xs top k = match xs with
  | [] -> k 1
  | 0::_ -> top 0
  | x::xs -> product_cps0 xs top (fun r -> k (x * r));;

#trace product_cps0;;

product_cps0 [1;2;0;4;5;6;7;8] (fun v -> v) (fun v -> v);;

let product_cps0_interface xs k =  product_cps0 xs k k;;
