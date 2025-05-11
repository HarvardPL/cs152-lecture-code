-- Datatype for arithmetic expressions
inductive Expr where
  | const : Int → Expr                 -- Constants like 5
  | var : String → Expr                -- Variables like "x"
  | add : Expr → Expr → Expr           -- Addition (e₁ + e₂)
  | mul : Expr → Expr → Expr           -- Multiplication (e₁ + e₂)
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
    | Expr.const 0, e => e            -- 0 + e => e
    | e, Expr.const 0 => e            -- e + 0 => e
    | _, _ => Expr.add e₁' e₂'        -- Otherwise keep the optimized addition
  | Expr.mul e₁ e₂ =>
    let e₁' := optimize e₁
    let e₂' := optimize e₂
    match e₁', e₂' with
    | Expr.const 0, _ => Expr.const 0 -- 0 * e => 0
    | _, Expr.const 0 => Expr.const 0 -- e * 0 => 0
    | Expr.const 1, e => e            -- 1 * e => e
    | e, Expr.const 1 => e            -- e * 1 => e
    | _, _ => Expr.mul e₁' e₂'        -- Otherwise keep the optimized multiplication

-- Theorem: optimizer preserves semantics
theorem optimize_preserves_semantics (e : Expr) (env : Env) :
  evaluate (optimize e) env = evaluate e env := by
  induction e with
  | const n =>
    -- Case: e = const n
    simp [optimize, evaluate]

  | var x =>
    -- Case: e = var x
    simp [optimize, evaluate]

  | add e₁ e₂ ih₁ ih₂ =>
    -- Case: e = e₁ + e₂
    simp [optimize]

    -- Use induction hypotheses
    have h₁ : evaluate (optimize e₁) env = evaluate e₁ env := ih₁
    have h₂ : evaluate (optimize e₂) env = evaluate e₂ env := ih₂

    -- Analyze all possible cases of optimize e₁ and optimize e₂
    simp [evaluate]

    -- Split into cases based on whether optimize e₁ is 0
    by_cases h_e1_zero : optimize e₁ = Expr.const 0
    · -- Case: optimize e₁ = 0
      simp [h_e1_zero, evaluate]
      -- Now optimize (e₁ + e₂) = optimize e₂
      rw [h₂]
      -- And evaluate e₁ = 0
      have : evaluate e₁ env = 0 := by
        rw [← h₁, h_e1_zero]
        simp [evaluate]
      rw [this]
      simp

    -- Split into cases based on whether optimize e₂ is 0
    by_cases h_e2_zero : optimize e₂ = Expr.const 0
    · -- Case: optimize e₂ = 0
      simp [h_e2_zero, evaluate]
      -- Now optimize (e₁ + e₂) = optimize e₁
      rw [h₁]
      -- And evaluate e₂ = 0
      have : evaluate e₂ env = 0 := by
        rw [← h₂, h_e2_zero]
        simp [evaluate]
      rw [this]
      simp

    -- General case: neither is zero
    -- Now we know optimize (e₁ + e₂) = Expr.add (optimize e₁) (optimize e₂)
    simp [evaluate]
    rw [h₁, h₂]

  | mul e₁ e₂ ih₁ ih₂ =>
    -- Case: e = e₁ * e₂
    simp [optimize]

    -- Use induction hypotheses
    have h₁ : evaluate (optimize e₁) env = evaluate e₁ env := ih₁
    have h₂ : evaluate (optimize e₂) env = evaluate e₂ env := ih₂

    -- Analyze all possible cases of optimize e₁ and optimize e₂
    simp [evaluate]

    -- Split into cases based on whether optimize e₁ is 0
    by_cases h_e1_zero : optimize e₁ = Expr.const 0
    · -- Case: optimize e₁ = 0
      simp [h_e1_zero, evaluate]
      rw [← h₁]
      rw [h_e1_zero]
      simp [evaluate]

    -- Split into cases based on whether optimize e₂ is 0
    by_cases h_e2_zero : optimize e₂ = Expr.const 0
    · -- Case: optimize e₂ = 0
      simp [h_e2_zero, evaluate]
      rw [← h₂]
      rw [h_e2_zero]
      simp [evaluate]

    -- Split into cases based on whether optimize e₁ is 1
    by_cases h_e1_one : optimize e₁ = Expr.const 1
    · -- Case: optimize e₁ = 1
      simp [h_e1_one, evaluate]
      rw [h₂]
      have : evaluate e₁ env = 1 := by
        rw [← h₁, h_e1_one]
        simp [evaluate]
      rw [this]
      simp

    -- Split into cases based on whether optimize e₂ is 1
    by_cases h_e2_one : optimize e₂ = Expr.const 1
    · -- Case: optimize e₂ = 1
      simp [h_e2_one, evaluate]
      rw [h₁]
      have : evaluate e₂ env = 1 := by
        rw [← h₂, h_e2_one]
        simp [evaluate]
      rw [this]
      simp

    -- General case:
    -- Now we know optimize (e₁ * e₂) = Expr.mul (optimize e₁) (optimize e₂)
    simp [evaluate]
    rw [h₁, h₂]
