import Mathlib.Tactic

structure Judgment (α β : Type _) where
  /-- The antecedents of the judgment. This is also called the context. -/
  left : List α
  /-- The consequent of the judgment. -/
  right : β

-- I don't know what priority this should be.
notation:10 l " ⊢ " r => Judgment.mk l r

/-- A deduction system, with given antecedent and consequent types,
assigns a type to each judgment, which is the type of proofs of that judgment.
If the universe parameter is `0`, the proofs of each judgment are propositions. -/
class DeductionSystem.{u} (α β : Type _) where
  proof : Judgment α β → Sort u

export DeductionSystem (proof)

variable [DeductionSystem α β]

/-- A deduction system has *permutation* if proofs are stable under permutation of the context. -/
class Permutation (α β : Type _) [DeductionSystem α β] where
  permute (Γ₁ : List α) (Γ₂ : List α) {C : β} (h : Γ₁ ~ Γ₂) :
    proof (Γ₁ ⊢ C) ≃ proof (Γ₂ ⊢ C)

export Permutation (permute)

section Permutation

variable [Permutation α β] {Γ Γ₁ Γ₂ : List α} {γ γ₁ γ₂ : α} {C : β}

/-- A way to cast between proofs where the contexts are equal only propositionally.
This has better computational properties than just using `Equiv.cast`. -/
def castProof (h : Γ₁ = Γ₂ := by simp) : proof (Γ₁ ⊢ C) ≃ proof (Γ₂ ⊢ C) :=
  permute Γ₁ Γ₂ (List.Perm.of_eq h)

def permuteSwap :
    proof (γ₁ :: γ₂ :: Γ ⊢ C) ≃ proof (γ₂ :: γ₁ :: Γ ⊢ C) :=
  permute _ _ (List.Perm.swap γ₂ γ₁ Γ)

def permuteMiddle :
    proof (Γ₁ ++ γ :: Γ₂ ⊢ C) ≃ proof (γ :: (Γ₁ ++ Γ₂) ⊢ C) :=
  permute _ _ List.perm_middle

def permuteAppend :
    proof (Γ₁ ++ Γ₂ ⊢ C) ≃ proof (Γ₂ ++ Γ₁ ⊢ C) :=
  permute _ _ (List.perm_append_comm)

end Permutation

/-- A deduction system has *weakening* if proofs are stable under increasing the context. -/
class Weakening (α β : Type _) [DeductionSystem α β] where
  weaken' (Γ₁ Γ₂ : List α) (C : β) :
    proof (Γ₁ ⊢ C) → proof (Γ₂ ++ Γ₁ ⊢ C)

/-- A deduction system has *contraction* if a duplicate hypothesis can be removed. -/
class Contraction (α β : Type _) [DeductionSystem α β] where
  contract' (Γ : List α) (γ : α) (C : β) (h : γ ∈ Γ) :
    proof (γ :: Γ₁ ⊢ C) → proof (Γ₁ ⊢ C)

export Contraction (contract')

/-- The *contraction* rule for multiple hypotheses. -/
def contract [Contraction α β] :
    (Γ₁ Γ₂ : List α) → (C : β) → (h : Γ₁ ⊆ Γ₂) →
    proof (Γ₁ ++ Γ₂ ⊢ C) → proof (Γ₂ ⊢ C)
  | [], _, _, _, pf => pf
  | γ :: Γ₁, Γ₂, C, h, pf =>
      contract Γ₁ Γ₂ C (by aesop) (contract' (Γ₁ ++ Γ₂) γ C (by aesop) pf)

/-- The *weakening* rule, expressed using contraction and permutation:
we can weaken the hypotheses of a proof to any superset of hypotheses.
Note that the list subset operation does not count multiplicity, so we need contraction. -/
def weaken [Weakening α β] [Permutation α β] [Contraction α β]
    (Γ₁ Γ₂ : List α) (C : β) (h : Γ₁ ⊆ Γ₂) :
    proof (Γ₁ ⊢ C) → proof (Γ₂ ⊢ C) :=
  contract Γ₁ Γ₂ C h ∘ permuteAppend ∘ Weakening.weaken' Γ₁ Γ₂ C
