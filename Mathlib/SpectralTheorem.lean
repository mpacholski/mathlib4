import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

-- import Mathlib.MeasureTheory.Integral.Lebesgue
-- import Mathlib.Analysis.InnerProductSpace.Dual

import Mathlib.Algebra.Star.StarAlgHom


section ContinuousFunctionalCalculus

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) -- (hA' : IsBoundedLinearMap ℂ A)

variable (f : ℝ → ℝ)

-- 2. Lean synthesizes the normal functional calculus over ℂ
instance : ContinuousFunctionalCalculus ℂ (H →L[ℂ] H) IsStarNormal where
  exists_cfc_of_predicate a ha := by
    constructor
    · sorry
    · sorry
  spectrum_nonempty a ha := by
    sorry
  predicate_zero := sorry

end ContinuousFunctionalCalculus
