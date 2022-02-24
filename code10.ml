type 'a tree =
  | Leaf of 'a
  | Node of ('a tree * 'a tree);;
           
(* success continuation *)
(* failure continuation *)

let rec dfs tree predicate success failure =
  match tree with
  | Leaf elem -> if (predicate elem) then (success elem) else (failure ())
  | Node (left, right) -> dfs left predicate success (fun () -> dfs right predicate success failure);;

exception Not_Found;;

let search tree predicate =
  dfs tree predicate (fun x -> x) (fun () -> raise Not_Found);;

search (Node (Leaf 1, (Node (Leaf 2, Leaf 3)))) (fun n -> n mod 2 == 0);;
