/-
We use a sigma type (`Σ'`) rather than existential quantification (`∃`).

The key difference is:
* `∃ x, P x` lives in `Prop`
* `Σ x, P x` lives in `Type`

So a sigma term can be used as ordinary data.
-/
def divisionData (x y : Nat) (h : 0 < y) :
  Σ' q : Nat, Σ' r : Nat, (x = y * q + r) ∧ r < y := by
  refine ⟨x / y, x % y, ?_⟩
  constructor
  · rw [Nat.add_comm, Nat.mod_add_div]
  · exact Nat.mod_lt _ h

def quotient (x y : Nat) (h : 0 < y) : Nat :=
-- Project the witness out of the sigma type
  (divisionData x y h).1

def remainder (x y : Nat) (h : 0 < y) : Nat :=
  (divisionData x y h).2.1

#eval quotient 17 5 (by decide)
#eval remainder 17 5 (by decide)

theorem quotient_remainder_spec (x y : Nat) (h : 0 < y) :
    x = y * quotient x y h + remainder x y h ∧ remainder x y h < y :=
  (divisionData x y h).2.2

example : ∃ z : Nat, z = 3 := by
  exact ⟨3, rfl⟩
