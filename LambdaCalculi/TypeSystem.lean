import LambdaCalculi.DeductionSystem

/-- Note: The `outParam` markers on this class ensure that typeclass synthesis depends on
the type of terms. This has the downside that we can't extend a `DeductionSystem α β`. -/
class TypeSystemData (α β : outParam <| Type _) (Λ : Type _) (V T : outParam <| Type _) where
  /-- A proposition representing the assertion that a variable has a given type. -/
  varTy : V → T → α
  /-- A proposition representing the assertion that a term has a given type. -/
  termTy : Λ → T → β

  /-- Each variable is naturally a term. -/
  var : V → Λ
  /-- The set of free variables of a term. -/
  free : Λ → Set V
  /-- Substitute a variable for a term inside another term. -/
  subst : V → Λ → Λ → Λ

export TypeSystemData (var free)

-- I don't know what priority these should be.
-- I also don't really like the elaboration of variable typing assertions.
notation:60 v " ∶[" Λ "] " τ => TypeSystemData.varTy Λ v τ
notation:60 t " ∶ " τ => TypeSystemData.termTy t τ
notation:80 t "[" v " := " s "]" => TypeSystemData.subst v s t

class TypeSystem (α β : outParam <| Type _) (Λ : Type _) (V T : outParam <| Type _)
    [DeductionSystem α β] extends TypeSystemData α β Λ V T where
  ax {v : V} : proof ([v ∶[Λ] τ] ⊢ var v ∶ τ)
  free_var : free (var v) = {v}
  subst_var : (var v)[v := t] = t
  subst_var_ne : v ≠ w → (var w)[v := t] = var w
  subst_eq_of_not_free : v ∉ free t → t[v := s] = t
  free_subst_of_free : v ∈ free t → free (t[v := s]) = (free t \ {v}) ∪ free s

export TypeSystem (free_var subst_var subst_var_ne subst_eq_of_not_free free_subst_of_free)

attribute [simp] free_var subst_var

variable [DeductionSystem α β] [TypeSystem α β Λ V T]

theorem free_subst_of_not_free {t : Λ} (h : v ∉ free t) : free (t[v := s]) = free t :=
  by rw [subst_eq_of_not_free h]

theorem free_subst_eq {t : Λ} :
    free (t[v := s]) = (free t \ {v}) ∪ {w ∈ free s | v ∈ free t} := by
  by_cases h : v ∈ free t
  · simp [free_subst_of_free, h]
  · simp [subst_eq_of_not_free, h]

theorem not_mem_free_of_subst {t : Λ} (h : v ∉ free s) : v ∉ free (t[v := s]) := by
  rw [free_subst_eq]
  simp_all
