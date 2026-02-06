-- Thanks to Arthur Adjedj for helping with the proofs

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
set_option grind.warning false
theorem optimize_preserves_semantics (e : Expr) (env : Env) :
  evaluate (optimize e) env = evaluate e env := by
  induction e <;> simp [optimize, evaluate]
  <;> grind +ring [optimize, evaluate]

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

-- Theorem: optimizer produces optimital expressions
theorem optimize_optimal (e : Expr) :
  optimal (optimize e) := by
  induction e <;> simp [optimize, optimal] <;> split <;> simp [optimal, *]

-- Compiler correctness proof for a stack machine
-- See also: https://xavierleroy.org/courses/EUTypes-2019/

-- Stack machine instructions
inductive Instr where
  | push : Int → Instr        -- Push a constant onto the stack
  | load : String → Instr     -- Load a variable onto the stack
  | add : Instr               -- Pop two values, push their sum
  | mul : Instr               -- Pop two values, push their product
  deriving Repr

-- Compile expression to stack machine code
def compile : Expr → List Instr
  | Expr.const n => [Instr.push n]
  | Expr.var x => [Instr.load x]
  | Expr.add e₁ e₂ => compile e₁ ++ compile e₂ ++ [Instr.add]
  | Expr.mul e₁ e₂ => compile e₁ ++ compile e₂ ++ [Instr.mul]

-- Execute stack machine code, returning None on stack underflow
def exec : List Instr → List Int → Env → Option (List Int)
  | [], stk, _ => some stk
  | Instr.push v :: code, stk, env => exec code (v :: stk) env
  | Instr.load x :: code, stk, env => exec code (env x :: stk) env
  | Instr.add :: code, v₂ :: v₁ :: stk, env => exec code ((v₁ + v₂) :: stk) env
  | Instr.mul :: code, v₂ :: v₁ :: stk, env => exec code ((v₁ * v₂) :: stk) env
  | Instr.add :: _, _, _ => none  -- Stack underflow
  | Instr.mul :: _, _, _ => none  -- Stack underflow

-- Key lemma: exec distributes over code concatenation
theorem exec_append (code₁ code₂ : List Instr) (stk : List Int) (env : Env) :
  exec (code₁ ++ code₂) stk env =
    match exec code₁ stk env with
    | some stk' => exec code₂ stk' env
    | none => none := by
  induction code₁ generalizing stk with
  | nil => simp [exec]
  | cons instr code₁ ih =>
    cases instr with
    | push v => simp [exec, ih]
    | load x => simp [exec, ih]
    | add =>
      cases stk with
      | nil => simp [exec]
      | cons v₂ stk' =>
        cases stk' with
        | nil => simp [exec]
        | cons v₁ stk'' => simp [exec, ih]
    | mul =>
      cases stk with
      | nil => simp [exec]
      | cons v₂ stk' =>
        cases stk' with
        | nil => simp [exec]
        | cons v₁ stk'' => simp [exec, ih]

-- Key insight: compile preserves semantics with any continuation stack
theorem compile_correct (e : Expr) (code : List Instr) (stk : List Int) (env : Env) :
  exec (compile e ++ code) stk env = exec code (evaluate e env :: stk) env := by
  induction e generalizing code stk with
  | const n => simp [compile, exec, evaluate]
  | var x => simp [compile, exec, evaluate]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [compile, evaluate, List.append_assoc]
    rw [ih₁]
    rw [ih₂]
    simp [exec]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [compile, evaluate, List.append_assoc]
    rw [ih₁]
    rw [ih₂]
    simp [exec]

-- Main theorem: compiled code succeeds and evaluates correctly
theorem compiler_correct (e : Expr) (env : Env) :
  exec (compile e) [] env = some [evaluate e env] := by
  have h := compile_correct e [] [] env
  simp at h
  exact h

-- Concrete example: 2 + (3 * 4) = 14
#eval
  let e := Expr.add (Expr.const 2) (Expr.mul (Expr.const 3) (Expr.const 4))
  let env : Env := fun _ => 0
  (compile e, exec (compile e) [] env, evaluate e env)
