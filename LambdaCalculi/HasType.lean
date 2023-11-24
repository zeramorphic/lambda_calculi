import LambdaCalculi.Context

namespace LambdaCalculi

/-!
# Types of λ-terms

We define the typability relation on λ-terms by induction.
To allow for the study of untyped λ-terms, we do not bake type correctness into the definition of
λ-terms, so there may be λ-terms that are ill-typed.
-/

variable {p : LambdaParams} {U C : Type _}

@[mk_iff]
inductive HasType (T : C → LambdaType p U) : Context p U → LambdaTerm p U C → LambdaType p U → Prop
| const : HasType T Γ (.const c) (T c)
| var (h : n < Γ.length) : HasType T Γ (.var n) (Γ.get ⟨n, h⟩)
| lambda : HasType T (τ :: Γ) t σ → HasType T Γ (.lambda h τ t) (.lambda h τ σ)
| app : HasType T Γ l (.lambda h τ σ) → HasType T Γ r τ → HasType T Γ (.app h l r) σ
| pair : HasType T Γ l σ → HasType T Γ r τ → HasType T Γ (.pair h l r) (.prod h σ τ)
| fst : HasType T Γ t (.prod h σ τ) → HasType T Γ (.fst h t) σ
| snd : HasType T Γ t (.prod h σ τ) → HasType T Γ (.snd h t) τ
| inl : HasType T Γ l σ → HasType T Γ (.inl h τ l) (.coprod h σ τ)
| inr : HasType T Γ r τ → HasType T Γ (.inr h σ r) (.coprod h σ τ)
| case : HasType T Γ t (.coprod h τ₁ τ₂) → HasType T (τ₁ :: Γ) l σ → HasType T (τ₂ :: Γ) r σ →
    HasType T Γ (.case h l r t) σ
| star : HasType T Γ (.star h) (.unit h)
| elim : HasType T Γ t (.empty h) → HasType T Γ (.elim h τ t) τ

notation:20 Γ " ⊢[" T "] " t " ∶ " τ => HasType T Γ t τ

@[simp]
theorem hasType_const : (Γ ⊢[T] .const c ∶ σ) ↔ σ = T c := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .const

@[simp]
theorem hasType_var : (Γ ⊢[T] .var n ∶ σ) ↔ ∃ h : n < Γ.length, σ = Γ.get ⟨n, h⟩ := by
  constructor
  · intro h
    cases h
    exact ⟨_, rfl⟩
  · rintro ⟨h, rfl⟩
    exact .var h

@[simp]
theorem hasType_lambda : (Γ ⊢[T] .lambda h ρ t ∶ τ) ↔
    ∃ σ, τ = .lambda h ρ σ ∧ (ρ :: Γ ⊢[T] t ∶ σ) := by
  constructor
  · intro h
    cases h
    exact ⟨_, rfl, by assumption⟩
  · rintro ⟨σ, rfl, h⟩
    exact .lambda h

@[simp]
theorem hasType_app : (Γ ⊢[T] .app h t u ∶ τ) ↔
    ∃ σ, (Γ ⊢[T] t ∶ .lambda h σ τ) ∧ (Γ ⊢[T] u ∶ σ) := by
  constructor
  · intro h
    cases h
    exact ⟨_, by assumption, by assumption⟩
  · rintro ⟨σ, h₁, h₂⟩
    exact .app h₁ h₂

@[simp]
theorem hasType_pair : (Γ ⊢[T] .pair h t u ∶ τ) ↔
    ∃ σ₁ σ₂, τ = .prod h σ₁ σ₂ ∧ (Γ ⊢[T] t ∶ σ₁) ∧ (Γ ⊢[T] u ∶ σ₂) := by
  constructor
  · intro h
    cases h
    exact ⟨_, _, rfl, by assumption, by assumption⟩
  · rintro ⟨σ₁, σ₂, rfl, h₁, h₂⟩
    exact .pair h₁ h₂

@[simp]
theorem hasType_fst : (Γ ⊢[T] .fst h t ∶ τ) ↔
    ∃ σ, (Γ ⊢[T] t ∶ .prod h τ σ) := by
  constructor
  · intro h
    cases h
    exact ⟨_, by assumption⟩
  · rintro ⟨σ, h⟩
    exact .fst h

@[simp]
theorem hasType_snd : (Γ ⊢[T] .snd h t ∶ τ) ↔
    ∃ σ, (Γ ⊢[T] t ∶ .prod h σ τ) := by
  constructor
  · intro h
    cases h
    exact ⟨_, by assumption⟩
  · rintro ⟨σ, h⟩
    exact .snd h

@[simp]
theorem hasType_inl : (Γ ⊢[T] .inl h τ t ∶ σ) ↔
    ∃ ρ, σ = .coprod h ρ τ ∧ (Γ ⊢[T] t ∶ ρ) := by
  constructor
  · intro h
    cases h
    exact ⟨_, rfl, by assumption⟩
  · rintro ⟨σ, rfl, h⟩
    exact .inl h

@[simp]
theorem hasType_inr : (Γ ⊢[T] .inr h τ t ∶ σ) ↔
    ∃ ρ, σ = .coprod h τ ρ ∧ (Γ ⊢[T] t ∶ ρ) := by
  constructor
  · intro h
    cases h
    refine ⟨_, rfl, by assumption⟩
  · rintro ⟨σ, rfl, h⟩
    exact .inr h

@[simp]
theorem hasType_case : (Γ ⊢[T] .case h l r t ∶ σ) ↔
    ∃ τ₁ τ₂, (Γ ⊢[T] t ∶ .coprod h τ₁ τ₂) ∧ (τ₁ :: Γ ⊢[T] l ∶ σ) ∧ (τ₂ :: Γ ⊢[T] r ∶ σ) := by
  constructor
  · intro h
    cases h
    refine ⟨_, _, by assumption, by assumption, by assumption⟩
  · rintro ⟨τ₁, τ₂, h₁, h₂, h₃⟩
    exact .case h₁ h₂ h₃

@[simp]
theorem hasType_star : (Γ ⊢[T] .star h ∶ σ) ↔ σ = .unit h := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .star

@[simp]
theorem hasType_elim : (Γ ⊢[T] .elim h τ t ∶ σ) ↔ σ = τ ∧ (Γ ⊢[T] t ∶ .empty h) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, by assumption⟩
  · rintro ⟨rfl, h⟩
    exact .elim h

/-- The unique typing theorem. -/
theorem eq_of_hasType (hσ : Γ ⊢[T] t ∶ σ) (hτ : Γ ⊢[T] t ∶ τ) : σ = τ := by
  induction t generalizing Γ σ τ
  case const =>
    rw [hasType_const] at hσ hτ
    rw [hσ, hτ]
  case var =>
    rw [hasType_var] at hσ hτ
    obtain ⟨_, rfl⟩ := hσ
    obtain ⟨_, rfl⟩ := hτ
    rfl
  case lambda ih =>
    rw [hasType_lambda] at hσ hτ
    obtain ⟨_, rfl, hσ⟩ := hσ
    obtain ⟨_, rfl, hτ⟩ := hτ
    rw [ih hσ hτ]
  case app ih _ =>
    rw [hasType_app] at hσ hτ
    obtain ⟨_, h₁, -⟩ := hσ
    obtain ⟨_, h₂, -⟩ := hτ
    cases ih h₁ h₂
    rfl
  case pair ih₁ ih₂ =>
    rw [hasType_pair] at hσ hτ
    obtain ⟨σ₁, σ₂, rfl, h₁, h₂⟩ := hσ
    obtain ⟨τ₁, τ₂, rfl, h₁', h₂'⟩ := hτ
    rw [ih₁ h₁ h₁', ih₂ h₂ h₂']
  case fst ih | snd ih =>
    simp only [hasType_fst, hasType_snd] at hσ hτ
    obtain ⟨σ', hσ⟩ := hσ
    obtain ⟨τ', hτ⟩ := hτ
    cases ih hσ hτ
    rfl
  case inl ih | inr ih =>
    simp only [hasType_inl, hasType_inr] at hσ hτ
    obtain ⟨σ', rfl, hσ⟩ := hσ
    obtain ⟨τ', rfl, hτ⟩ := hτ
    cases ih hσ hτ
    rfl
  case case ih₁ _ ih =>
    rw [hasType_case] at hσ hτ
    obtain ⟨σ₁, σ₂, hσ, hσ₁, _⟩ := hσ
    obtain ⟨τ₁, τ₂, hτ, hτ₁, _⟩ := hτ
    cases ih hσ hτ
    cases ih₁ hσ₁ hτ₁
    rfl
  case star =>
    rw [hasType_star] at hσ hτ
    rw [hσ, hτ]
  case elim _ =>
    rw [hasType_elim] at hσ hτ
    rw [hσ.1, hτ.1]
