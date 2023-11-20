import LambdaCalculi.Logic

structure Typing (Λ T : Type _) where
  term : Λ
  type : T

notation:20 term " ∶ " type => Typing.mk term type

/-- A *type system* is a logic where the propositions are typing assertions. -/
abbrev TypeSystem (Λ T : Type _) := Logic (Typing Λ T)
