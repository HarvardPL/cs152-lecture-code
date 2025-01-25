inductive Exp
| EVar (x : String)
| EInt (v : Int)
| EAdd (e1 e2 : Exp)
| EMul (e1 e2 : Exp)
deriving Repr

-- Evaluation function
def eval (e : Exp) (env : String → Int) : Int :=
  match e with
  | Exp.EVar x  => env x
  | Exp.EInt v  => v
  | Exp.EAdd e1 e2 => eval e1 env + eval e2 env
  | Exp.EMul e1 e2 => eval e1 env * eval e2 env

-- Optimizer function
def optimize : Exp → Exp
| Exp.EVar x => Exp.EVar x
| Exp.EInt v => Exp.EInt v
| Exp.EAdd (Exp.EInt v1) (Exp.EInt v2) => Exp.EInt (v1 + v2)
| Exp.EAdd (Exp.EInt 0) e2 => optimize e2
| Exp.EAdd e1 (Exp.EInt 0) => optimize e1
| Exp.EAdd e1 e2 => Exp.EAdd (optimize e1) (optimize e2)
| Exp.EMul (Exp.EInt v1) (Exp.EInt v2) => Exp.EInt (v1 * v2)
| Exp.EMul (Exp.EInt 0) e2 => Exp.EInt 0
| Exp.EMul e1 (Exp.EInt 0) => Exp.EInt 0
| Exp.EMul (Exp.EInt 1) e2 => optimize e2
| Exp.EMul e1 (Exp.EInt 1) => optimize e1
| Exp.EMul e1 e2 => Exp.EMul (optimize e1) (optimize e2)

-- Proving that optimize preserves semantics
theorem optimizer_preserves_semantics (e : Exp) (env : String → Int) :
  eval (optimize e) env = eval e env :=
by
  induction e with
  | EVar x => rfl
  | EInt v => rfl
  | EAdd e1 e2 ih1 ih2 =>
      simp [optimize]
      cases e1 <;> cases e2 <;> simp [optimize, eval, ih1, ih2]
  | EMul e1 e2 ih1 ih2 =>
      simp [optimize]
      cases e1 <;> cases e2 <;> simp [optimize, eval, ih1, ih2]

-- Definition of optimality
def optimal : Exp → Bool
| Exp.EVar _ => true
| Exp.EInt _ => true
| Exp.EAdd (Exp.EInt _) (Exp.EInt _) => false
| Exp.EAdd (Exp.EInt 0) _ => false
| Exp.EAdd _ (Exp.EInt 0) => false
| Exp.EAdd e1 e2 => optimal e1 && optimal e2
| Exp.EMul (Exp.EInt _) (Exp.EInt _) => false
| Exp.EMul (Exp.EInt 0) _ => false
| Exp.EMul _ (Exp.EInt 0) => false
| Exp.EMul (Exp.EInt 1) _ => false
| Exp.EMul _ (Exp.EInt 1) => false
| Exp.EMul e1 e2 => optimal e1 && optimal e2

-- Proving that optimize always produces an optimal expression
theorem optimizer_is_optimal (e : Exp) : optimal (optimize e) :=
by sorry -- TODO
