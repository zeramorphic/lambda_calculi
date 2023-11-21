import LambdaCalculi.DeductionSystem

/-- For each term `t : Λ` and type `τ : T`, this class assigns a value of `α`, representing
this typing assertion. -/
class Typing (α : Type _) (Λ T : outParam <| Type _) where
  type : Λ → T → α

notation:20 term " ∶ " type => Typing.type term type

variable [Typing α V T] [Typing β Λ T] [DeductionSystem α β]
