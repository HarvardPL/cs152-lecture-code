/-
`Nat.div` is total in Lean: it does not crash on division by zero.
For natural numbers, Lean uses the convention `x / 0 = 0`.

The point is to make the *interface* state the precondition explicitly.
-/
def safeDiv (x y : Nat) (_ : 0 < y) : Nat :=
  x / y


#eval safeDiv 17 5 (by decide)  -- `by decide` proof that 0 < 5

def avgOfTwo (a b : Nat) : Nat := safeDiv (a + b) 2 (by decide)

def tryDiv (x y : Nat) : Option Nat :=
  if h : 0 < y then
    some (safeDiv x y h)
  else
    none

/--
A tiny dependently typed vector.
`Vec α n` means: a vector of elements of type `α` with length exactly `n`.
-/
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
deriving Repr

def ex1 (xs : Vec Bool (35 + 7)) : Vec Bool 42 := xs

-- def ex2 (xs : Vec Bool (n + m)) : Vec Bool (m + n) := xs
def ex2 (xs : Vec Bool (n + m)) : Vec Bool (m + n) := by
  rw [Nat.add_comm]
  exact xs

namespace Vec
/-- Convert a vector back to an ordinary list. -/
def toList : Vec α n → List α
  | nil => []
  | cons x xs => x :: toList xs

/-- Safe head: the type rules out the empty vector case. -/
def safeHead : Vec α (n + 1) → α
  | cons x _ => x

/-- Some concrete vectors. -/
def xs : Vec Nat 2 :=
  cons 10 (cons 20 nil)

def ys : Vec Nat 3 :=
  cons 30 (cons 40 (cons 50 nil))

#eval toList xs                 -- expected output: [10, 20]
#eval safeHead xs                   -- expected output: 10
example : safeHead xs = 10 := rfl

/-- Append preserves length in the result type.
  A direct definition is a bit trickier than it first looks,
  because the recursive cases require arithmetic rewrites on type indices.

  **This does not type-check directly**.
  def append : Vec α n → Vec α m → Vec α (n + m)
    | nil, ys => ys
    | cons x xs, ys => cons x (append xs ys)
-/

def appendAux : Vec α n → Vec α m → Vec α (m + n)
  | nil, ys => ys
    -- goal: Vec α (m + 0), which reduces to Vec α m
  | cons x xs, ys => cons x (appendAux xs ys)
    -- appendAux xs ys : Vec α (m + n)
    -- so cons gives Vec α (m + n + 1), matching the goal by reduction

def append (xs : Vec α n) (ys : Vec α m) : Vec α (n + m) := by
  -- appendAux returns length m + n; rewrite it to n + m
  rw [Nat.add_comm]
  apply (appendAux xs ys)


#eval toList (append xs ys)     -- expected output: [10, 20, 30, 40, 50]

end Vec
