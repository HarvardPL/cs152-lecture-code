-- Datatype for arithmetic expressions
inductive Expr where
  | const : Int → Expr                 -- Constants like 5
  | var : String → Expr                -- Variables like "x"
  | add : Expr → Expr → Expr           -- Addition (e₁ + e₂)
  | mul : Expr → Expr → Expr           -- Multiplication (e₁ * e₂)
  deriving Repr

-- Environment type (maps variable names to values)
def Env := String → Int

-- Evaluator function
def evaluate : Expr → Env → Int
  | Expr.const n, _ => n               -- A constant evaluates to itself
  | Expr.var x, env => env x           -- A variable evaluates to its value in the environment
  | Expr.add e₁ e₂, env => evaluate e₁ env + evaluate e₂ env  -- Addition evaluates recursively
  | Expr.mul e₁ e₂, env => evaluate e₁ env * evaluate e₂ env  -- Multiplication evaluates recursively too

-- Optimizer to remove additions by 0 & multiplication by 1, and to simplify multiplication by 0
def optimize : Expr → Expr
  | Expr.const n => Expr.const n       -- Constants remain unchanged
  | Expr.var x => Expr.var x           -- Variables remain unchanged
  | Expr.add e₁ e₂ =>
    let e₁' := optimize e₁
    let e₂' := optimize e₂
    match e₁', e₂' with
    | Expr.const n₁, Expr.const n₂ => Expr.const (n₁ + n₂)
    | Expr.const 0, e => e            -- 0 + e => e
    | e, Expr.const 0 => e            -- e + 0 => e
    | _, _ => Expr.add e₁' e₂'        -- Otherwise keep the optimized addition
  | Expr.mul e₁ e₂ =>
    let e₁' := optimize e₁
    let e₂' := optimize e₂
    match e₁', e₂' with
    | Expr.const n₁, Expr.const n₂ => Expr.const (n₁ * n₂)
    | Expr.const 0, _ => Expr.const 0 -- 0 * e => 0
    | _, Expr.const 0 => Expr.const 0 -- e * 0 => 0
    | Expr.const 1, e => e            -- 1 * e => e
    | e, Expr.const 1 => e            -- e * 1 => e
    | _, _ => Expr.mul e₁' e₂'        -- Otherwise keep the optimized multiplication


-- Theorem: optimizer preserves semantics
-- Thanks to Arthur Adjedj for pointing out the new grind tactic
set_option grind.warning false
theorem optimize_preserves_semantics (e : Expr) (env : Env) :
  evaluate (optimize e) env = evaluate e env := by
  induction e <;> simp [optimize, evaluate]
  <;> grind (config := {  ring := true }) [evaluate, optimize]

-- Predicate defining an optimally optimized expression
def optimal : Expr → Bool
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add (Expr.const _) (Expr.const _) => false
  | Expr.add (Expr.const 0) _ => false
  | Expr.add _ (Expr.const 0) => false
  | Expr.add e₁ e₂ => optimal e₁ && optimal e₂
  | Expr.mul (Expr.const _) (Expr.const _) => false
  | Expr.mul (Expr.const 0) _ => false
  | Expr.mul _ (Expr.const 0) => false
  | Expr.mul (Expr.const 1) _ => false
  | Expr.mul _ (Expr.const 1) => false
  | Expr.mul e₁ e₂ => optimal e₁ && optimal e₂

theorem optimize_optimal (e : Expr) (env : Env) :
  optimal (optimize e) := by
  induction e <;> simp [optimal, optimize, evaluate]
  · sorry -- addition
  · sorry -- multiplication
