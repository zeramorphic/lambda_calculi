import Mathlib.Tactic

namespace LambdaCalculi

/-!
# λ-calculi
-/

/-- A collection of Boolean parameters that determine which features of the λ-calculus we construct
should be enabled. See `BoxIntegral.IntegrationParams` for an application of this idea that is
already in mathlib. -/
@[ext]
structure LambdaParams where
  /-- This λ-calculus has λ-abstractions and applications. -/
  lambda : Bool
  /-- This λ-calculus has binary products and projections. -/
  prod : Bool
  /-- This λ-calculus has binary coproducts and a case split construction. -/
  coprod : Bool
  /-- This λ-calculus has a unit type and a constructor for that element. -/
  unit : Bool
  /-- This λ-calculus has an empty type and a recursor for it. -/
  empty : Bool

/-- Types of terms in a λ-calculus with parameters `p` and primitive types `U`. -/
inductive LambdaType (p : LambdaParams) (U : Type _)
| prim    : U → LambdaType p U
| lambda  : p.lambda  → LambdaType p U → LambdaType p U → LambdaType p U
| prod    : p.prod    → LambdaType p U → LambdaType p U → LambdaType p U
| coprod  : p.coprod  → LambdaType p U → LambdaType p U → LambdaType p U
| unit    : p.unit    → LambdaType p U
| empty   : p.empty   → LambdaType p U

/-- Terms in a λ-calculus with parameters `p`, primitive types `U` and opaque constants `C`. -/
inductive LambdaTerm (p : LambdaParams) (U C : Type _) : Type _
/-- An opaque constant. -/
| const : C → LambdaTerm p U C
/-- A local variable of a given de Bruijn index. -/
| var : ℕ → LambdaTerm p U C
/-- A λ-abstraction. -/
| lambda : p.lambda → LambdaType p U → LambdaTerm p U C → LambdaTerm p U C
/-- A λ-application. -/
| app : p.lambda → LambdaTerm p U C → LambdaTerm p U C → LambdaTerm p U C
/-- The pairing operation. -/
| pair : p.prod → LambdaTerm p U C → LambdaTerm p U C → LambdaTerm p U C
/-- The left projection of a product. -/
| fst : p.prod → LambdaTerm p U C → LambdaTerm p U C
/-- The right projection of a product. -/
| snd : p.prod → LambdaTerm p U C → LambdaTerm p U C
/-- The left injection of a coproduct. The type of the right factor is also given. -/
| inl : p.coprod → LambdaType p U → LambdaTerm p U C → LambdaTerm p U C
/-- The right injection of a coproduct. The type of the left factor is also given. -/
| inr : p.coprod → LambdaType p U → LambdaTerm p U C → LambdaTerm p U C
/-- Case splitting. If the parameters are `l`, `r`, `x`, then this term β-reduces to `l[t]` if
`x = inl t`, and β-reduces to `r[t]` if `x = inr t`, where square brackets denote instantiation of
the first de Bruijn index. This matches `Sum.rec`. -/
| case : p.coprod → LambdaTerm p U C → LambdaTerm p U C → LambdaTerm p U C → LambdaTerm p U C
/-- The inhabitant of the unit type. -/
| star : p.unit → LambdaTerm p U C
/-- The recursor for the empty type. This eliminates an element of `empty` into any given type. -/
| elim : p.empty → LambdaType p U → LambdaTerm p U C → LambdaTerm p U C

namespace LambdaTerm

variable {p : LambdaParams} {U C : Type _}

/-- Returns the smallest `R` such that the de Bruijn index of all free variables occurring in the
argument is strictly smaller than `R`. -/
def freeVarRange : LambdaTerm p U C → ℕ
| const _ => 0
| var n => n + 1
| lambda _ _ t => t.freeVarRange - 1
| app _ l r => max l.freeVarRange r.freeVarRange
| pair _ l r => max l.freeVarRange r.freeVarRange
| fst _ x => x.freeVarRange
| snd _ x => x.freeVarRange
| inl _ _ x => x.freeVarRange
| inr _ _ x => x.freeVarRange
| case _ l r t => max (max l.freeVarRange r.freeVarRange - 1) t.freeVarRange
| star _ => 0
| elim _ _ x => x.freeVarRange

@[simp]
theorem freeVarRange_const :
    (const c : LambdaTerm p U C).freeVarRange = 0 :=
  rfl

@[simp]
theorem freeVarRange_var :
    (var n : LambdaTerm p U C).freeVarRange = n + 1 :=
  rfl

@[simp]
theorem freeVarRange_lambda :
    (lambda h τ t : LambdaTerm p U C).freeVarRange = t.freeVarRange - 1 :=
  rfl

@[simp]
theorem freeVarRange_app :
    (app h l r : LambdaTerm p U C).freeVarRange = max l.freeVarRange r.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_pair :
    (pair h l r : LambdaTerm p U C).freeVarRange = max l.freeVarRange r.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_fst :
    (fst h l : LambdaTerm p U C).freeVarRange = l.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_snd :
    (snd h r : LambdaTerm p U C).freeVarRange = r.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_inl :
    (inl h τ l : LambdaTerm p U C).freeVarRange = l.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_inr :
    (inr h τ r : LambdaTerm p U C).freeVarRange = r.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_case :
    (case h l r t : LambdaTerm p U C).freeVarRange =
      max (max l.freeVarRange r.freeVarRange - 1) t.freeVarRange :=
  rfl

@[simp]
theorem freeVarRange_star :
    (star h : LambdaTerm p U C).freeVarRange = 0 :=
  rfl

@[simp]
theorem freeVarRange_elim :
    (elim h τ t : LambdaTerm p U C).freeVarRange = t.freeVarRange :=
  rfl

def Closed (t : LambdaTerm p U C) : Prop :=
  t.freeVarRange = 0

theorem closed_of_freeVarRange_le_zero {t : LambdaTerm p U C} (h : t.freeVarRange ≤ 0) :
    t.Closed :=
  Nat.le_zero.mp h

theorem Closed.freeVarRange_le_zero {t : LambdaTerm p U C} (h : t.Closed) :
    t.freeVarRange ≤ 0 :=
  Nat.le_zero.mpr h

section replace

/-- `n` is the de Bruijn index offset. -/
def replace' (f : ℕ → LambdaTerm p U C → Option (LambdaTerm p U C)) (n : ℕ)
    (t : LambdaTerm p U C) : LambdaTerm p U C :=
  match f n t with
  | some u => u
  | none =>
      match t with
      | const c => const c
      | var n => var n
      | lambda h τ t => lambda h τ (t.replace' f (n + 1))
      | app h l r => app h (l.replace' f n) (r.replace' f n)
      | pair h l r => pair h (l.replace' f n) (r.replace' f n)
      | fst h t => fst h (t.replace' f n)
      | snd h t => snd h (t.replace' f n)
      | inl h τ l => inl h τ (l.replace' f n)
      | inr h τ r => inr h τ (r.replace' f n)
      | case h l r t => case h (l.replace' f (n + 1)) (r.replace' f (n + 1)) (t.replace' f n)
      | star h => star h
      | elim h τ t => elim h τ (t.replace' f n)

variable {f : ℕ → LambdaTerm p U C → Option (LambdaTerm p U C)}

theorem replace'_some (h : f n t = some u) :
    replace' f n t = u := by
  cases t <;> simp only [h, replace']

@[simp]
theorem replace'_const :
  replace' f n (const c) = match f n (const c) with
    | some u => u
    | none => const c :=
  by simp only [replace']

@[simp]
theorem replace'_var :
  replace' f n (var m) = match f n (var m) with
    | some u => u
    | none => var m :=
  by simp only [replace']

@[simp]
theorem replace'_lambda :
  replace' f n (lambda h τ t) = match f n (lambda h τ t) with
    | some u => u
    | none => lambda h τ (t.replace' f (n + 1)) :=
  by simp only [replace']

@[simp]
theorem replace'_app :
  replace' f n (app h l r) = match f n (app h l r) with
    | some u => u
    | none => app h (l.replace' f n) (r.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_pair :
  replace' f n (pair h l r) = match f n (pair h l r) with
    | some u => u
    | none => pair h (l.replace' f n) (r.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_fst :
  replace' f n (fst h t) = match f n (fst h t) with
    | some u => u
    | none => fst h (t.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_snd :
  replace' f n (snd h t) = match f n (snd h t) with
    | some u => u
    | none => snd h (t.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_inl :
  replace' f n (inl h τ l) = match f n (inl h τ l) with
    | some u => u
    | none => inl h τ (l.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_inr :
  replace' f n (inr h τ r) = match f n (inr h τ r) with
    | some u => u
    | none => inr h τ (r.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_case :
  replace' f n (case h l r t) = match f n (case h l r t) with
    | some u => u
    | none => case h (l.replace' f (n + 1)) (r.replace' f (n + 1)) (t.replace' f n) :=
  by simp only [replace']

@[simp]
theorem replace'_star :
  replace' f n (star h) = match f n (star h) with
    | some u => u
    | none => star h :=
  by simp only [replace']

@[simp]
theorem replace'_elim :
  replace' f n (elim h τ t) = match f n (elim h τ t) with
    | some u => u
    | none => elim h τ (t.replace' f n) :=
  by simp only [replace']

def replace (f : ℕ → LambdaTerm p U C → Option (LambdaTerm p U C)) :
    LambdaTerm p U C → LambdaTerm p U C :=
  replace' f 0

end replace

def instantiateFun (t : LambdaTerm p U C) (n : ℕ) : LambdaTerm p U C → Option (LambdaTerm p U C)
| var m => some <|
    if m = n then
      t
    else if m < n then
      var m
    else
      var (m - 1)
| _ => none

/-- Replaces the variable corresponding to the first de Bruijn index with `t`. -/
def instantiate (t : LambdaTerm p U C) : LambdaTerm p U C → LambdaTerm p U C :=
  replace t.instantiateFun

theorem instantiate'_eq_of_freeVarRange_le {t : LambdaTerm p U C} (u : LambdaTerm p U C)
    (n : ℕ) (h : u.freeVarRange ≤ n) :
    replace' t.instantiateFun n u = u := by
  induction u generalizing n <;> rw [freeVarRange] at h
  case var m =>
    rw [Nat.add_one_le_iff] at h
    rw [replace'_var, instantiateFun]
    aesop
  all_goals aesop

theorem instantiate_eq_of_closed {t : LambdaTerm p U C} (u : LambdaTerm p U C) (h : u.Closed) :
    instantiate t u = u :=
  instantiate'_eq_of_freeVarRange_le u 0 h.freeVarRange_le_zero

def liftFun (n : ℕ) : LambdaTerm p U C → Option (LambdaTerm p U C)
| var m => if n ≤ m then some (var (m + 1)) else none
| _ => none

/-- Lifts the free variables in `t` up by one index. -/
def lift : LambdaTerm p U C → LambdaTerm p U C :=
  replace liftFun

theorem lift'_eq_of_freeVarRange_le (u : LambdaTerm p U C)
    (n : ℕ) (h : u.freeVarRange ≤ n) :
    replace' liftFun n u = u := by
  induction u generalizing n <;> rw [freeVarRange] at h
  case var m =>
    rw [Nat.add_one_le_iff] at h
    rw [replace'_var, liftFun]
    simp only
    rw [if_neg]
    rw [not_le]
    exact h
  all_goals aesop

theorem lift_eq_of_closed (t : LambdaTerm p U C) (h : t.Closed) :
    lift t = t :=
  lift'_eq_of_freeVarRange_le t 0 h.freeVarRange_le_zero

end LambdaTerm
