Inductive boolvec: nat -> Type :=
| boolvec_z: boolvec 0
| boolvec_s: forall n, boolvec n -> bool -> boolvec (S n).

Fixpoint natToPair(n: nat): Type :=
  match n with
  | O => unit
  | S m => bool * natToPair m
  end.

Fixpoint asPairs n (bv: boolvec n): natToPair n :=
  match bv with
  | boolvec_z => tt
  | boolvec_s n bv b => (b, asPairs n bv)
  end.

Compute (asPairs 1 (boolvec_s 0 boolvec_z true)).
Compute (asPairs 2 (boolvec_s 1 (boolvec_s 0 boolvec_z true) false)).
Compute natToPair 2.
