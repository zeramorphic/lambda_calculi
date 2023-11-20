import LambdaCalculi.DeductionSystem

/-- A *logic* is a deduction system whose antecedents and consequents in a judgment
are the same type. This allows us to state rules such as the axiom schema, and clearly define
concepts such as conjunctions and disjunctions. Typically, logics are taken to have the
permutation rule, but need not have weakening or contraction. -/
abbrev Logic (α : Type _) := DeductionSystem α α

abbrev Permutation (α : Type _) [Logic α] := PermutationSystem α α
abbrev Weakening (α : Type _) [Logic α] := WeakeningSystem α α
abbrev Contraction (α : Type _) [Logic α] := ContractionSystem α α
