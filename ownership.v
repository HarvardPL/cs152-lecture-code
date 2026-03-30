From iris.heap_lang Require Import lang adequacy total_adequacy proofmode notation.
From iris.prelude Require Import options.

(*** Separation logic can be used to track ownership.

     Since ownership cannot be duplicated and can only be consumed once,
     it provides a natural way to model the behavior of pointers.

     Let us look at a simple Rust example.
     We create a box, pass it to a function that updates the value and
     returns ownership, and then pass it to another function that consumes
     the box and returns the stored value.

     In sepatation logic, a heap assertion of the form [l ↦ #v] represents exclusive
     ownership of a heap cell [l] containing the value [v].
 *)

(** Rust

    fn increment_then_return(mut b: Box<i32>) -> Box<i32> {
        *b += 1;
        b
    }

    fn consume(b: Box<i32>) -> i32 {
        *b
    }

    fn main() -> i32 {
        let b = Box::new(41);
        let x = increment_then_return(b);
        consume(x)
    }

 *)

Section example.
  Context `{!heapGS Σ}.

  Definition increment_then_return : val :=
    λ: "b",
      "b" <- !"b" + #1;;
      "b".

  Definition consume : val :=
    λ: "b",
      let: "x" := !"b" in
      Free "b";;
      "x".

  Definition main : expr :=
    let: "b" := ref #41 in
    let: "x" := increment_then_return "b" in
    consume "x".

  (* This function takes ownership of the input location [l], updates the value,
    and returns ownership of the same location. *)

  Theorem increment_then_return_spec (l : loc) (v : Z) :
    {{{ l ↦ #v }}}
      increment_then_return #l
    {{{ RET #l; l ↦ #(v + 1) }}}.
  Proof.
    (* [Hl] is the current ownership of location [l];
      [Post] is the continuation for the postcondition. *)
    iIntros (Φ) "Hl Post".
    unfold increment_then_return.
    (* Symbolically execute the program. *)
    wp_pures.
    (* Load the current value from [l]. *)
    wp_load.
    wp_pures.
    (* Store the updated value [v + 1] back into [l]. *)
    wp_store.
    (* Return the same location [l], together with its updated ownership. *)
    by iApply "Post".
  Qed.

  (* This function consumes ownership of the input location [l],
    deallocates it, and returns the value that was stored in it. *)
  Theorem consume_spec (l : loc) (v : Z) :
    {{{ l ↦ #v }}}
      consume #l
    {{{ RET #v; True }}}.
  Proof.
    (* [Hl] is the current ownership of location [l];
      [Post] is the continuation for the postcondition. *)
    iIntros (Φ) "Hl Post".
    unfold consume.
    wp_pures.
    (* Read the value before freeing the location. *)
    wp_load.
    wp_pures.
    (* Freeing [l] consumes the ownership resource [l ↦ #v]. *)
    wp_free.
    wp_pures.
    by iApply "Post".
  Qed.

  Theorem main_spec :
    {{{ True }}}
      main
    {{{ RET #42; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold main.
    (* Allocate a fresh heap cell initialized to 41. *)
    wp_alloc b as "Hb".
    wp_pures.
    (* Transfer ownership of [b] to [increment_then_return]. *)
    wp_bind (increment_then_return _).
    iApply (increment_then_return_spec with "Hb").
    iIntros "!> Hb".
    wp_pures.
    (* Transfer the returned ownership to [consume]. *)
    iApply (consume_spec with "Hb").
    by iApply "Post".
  Qed.

End example.
