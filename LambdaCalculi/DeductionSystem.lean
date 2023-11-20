import Mathlib.Tactic

structure Judgment (α β : Type _) where
  /-- The antecedents of the judgment. This is also called the context. -/
  left : List α
  /-- The consequent of the judgment. -/
  right : β

notation:10 l " ⊢ " r => Judgment.mk l r

/-- A deduction system, with given antecedent and consequent types,
assigns a type to each judgment, which is the type of proofs of that judgment.
If the universe parameter is `0`, the proofs of each judgment are propositions. -/
class DeductionSystem.{u} (α β : Type _) where
  proof : Judgment α β → Sort u
  /-- A way to cast between proofs where the contexts are equal only propositionally.
  This can be `Equiv.cast`, but there's often a better implementation that keeps
  nice computational properties. -/
  castProof (h : Γ₁ = Γ₂ := by simp) : proof (Γ₁ ⊢ C) ≃ proof (Γ₂ ⊢ C)

export DeductionSystem (proof castProof)

variable [DeductionSystem α β]

/-- A deduction system has *permutation* if proofs are stable under permutation of the context. -/
class PermutationSystem (α β : Type _) [DeductionSystem α β] where
  permute (Γ₁ : List α) (γ₁ γ₂ : α) (Γ₂ : List α) (C : β) :
    proof (Γ₁ ++ γ₁ :: γ₂ :: Γ₂ ⊢ C) ≃ proof (Γ₁ ++ γ₂ :: γ₁ :: Γ₂ ⊢ C)

export PermutationSystem (permute)

section Permutation

variable [PermutationSystem α β]

def permuteHead (γ₁ γ₂ : α) (Γ : List α) (C : β) :
    proof (γ₁ :: γ₂ :: Γ ⊢ C) ≃ proof (γ₂ :: γ₁ :: Γ ⊢ C) :=
  permute [] γ₁ γ₂ Γ C

def permuteConsAppend' : (Γ₁ Γ₂ : List α) → (γ : α) → (Γ₃ : List α) → (C : β) →
    proof (Γ₁ ++ Γ₂ ++ γ :: Γ₃ ⊢ C) ≃ proof (Γ₁ ++ γ :: Γ₂ ++ Γ₃ ⊢ C)
  | Γ₁, [], γ, Γ₂, C => castProof
  | Γ₁, γ' :: Γ₂, γ, Γ₃, C =>
      Equiv.trans (Equiv.trans castProof
          ((permuteConsAppend' (Γ₁ ++ [γ']) Γ₂ γ Γ₃ C).trans castProof))
        ((permute Γ₁ γ' γ (Γ₂ ++ Γ₃) C).trans castProof)

def permuteConsAppend (Γ₁ : List α) (γ : α) (Γ₂ : List α) (C : β) :
    proof (Γ₁ ++ γ :: Γ₂ ⊢ C) ≃ proof (γ :: Γ₁ ++ Γ₂ ⊢ C) :=
  permuteConsAppend' [] Γ₁ γ Γ₂ C

def permuteAppend : (Γ₁ Γ₂ : List α) → (C : β) →
    proof (Γ₁ ++ Γ₂ ⊢ C) ≃ proof (Γ₂ ++ Γ₁ ⊢ C)
  | [], Γ₂, C => castProof
  | γ :: Γ₁, Γ₂, C =>
      ((permuteConsAppend Γ₁ γ Γ₂ C).symm.trans (permuteAppend Γ₁ (γ :: Γ₂) C)).trans
      (permuteConsAppend Γ₂ γ Γ₁ C).symm

end Permutation

/-- A deduction system has *weakening* if proofs are stable under increasing the context. -/
class WeakeningSystem (α β : Type _) [DeductionSystem α β] where
  weaken' (Γ₁ Γ₂ : List α) (C : β) :
    proof (Γ₁ ⊢ C) → proof (Γ₂ ++ Γ₁ ⊢ C)

/-- A deduction system has *contraction* if a duplicate hypothesis can be removed. -/
class ContractionSystem (α β : Type _) [DeductionSystem α β] where
  contract (Γ : List α) (γ : α) (C : β) (h : γ ∈ Γ) :
    proof (γ :: Γ₁ ⊢ C) → proof (Γ₁ ⊢ C)

export ContractionSystem (contract)

def contract' [ContractionSystem α β] :
    (Γ₁ Γ₂ : List α) → (C : β) → (h : Γ₁ ⊆ Γ₂) →
    proof (Γ₁ ++ Γ₂ ⊢ C) → proof (Γ₂ ⊢ C)
  | [], _, _, _, pf => pf
  | γ :: Γ₁, Γ₂, C, h, pf =>
      contract' Γ₁ Γ₂ C (by aesop) (contract (Γ₁ ++ Γ₂) γ C (by aesop) pf)

/-- The *weakening* rule, expressed using contraction and permutation:
we can weaken the hypotheses of a proof to any superset of hypotheses.
Note that the list subset operation does not count multiplicity, so we need contraction. -/
def weaken [WeakeningSystem α β] [PermutationSystem α β] [ContractionSystem α β]
    (Γ₁ Γ₂ : List α) (C : β) (h : Γ₁ ⊆ Γ₂) :
    proof (Γ₁ ⊢ C) → proof (Γ₂ ⊢ C) :=
  contract' Γ₁ Γ₂ C h ∘ permuteAppend Γ₂ Γ₁ C ∘ WeakeningSystem.weaken' Γ₁ Γ₂ C
