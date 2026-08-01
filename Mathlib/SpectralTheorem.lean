import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

-- This import supplies the C⋆-algebra structure on bounded operators.
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.Star.StarAlgHom

-- import Mathlib.MeasureTheory.Integral.Lebesgue
-- import Mathlib.Analysis.InnerProductSpace.Dual

import Mathlib.Algebra.Star.StarAlgHom


section ContinuousFunctionalCalculus

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) -- (hA' : IsBoundedLinearMap ℂ A)

variable (f : ℝ → ℝ)

example : cfc (id : ℝ → ℝ) A = A := cfc_id ℝ A hA

example : cfc (fun x : ℝ ↦ x*x) A = A.comp A := by
  rw [← ContinuousLinearMap.mul_def A A]
  nth_rw 2 3 [← cfc_id ℝ A hA]
  apply cfc_mul id id A

end ContinuousFunctionalCalculus

section Phase1

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
variable (x : H)

noncomputable def spectralFunction_toFun (f : CompactlySupportedContinuousMap ℝ ℝ) :=
  (Complex.re ⟪x, cfc f A x⟫_ℂ)

-- -- Step 1: Define the Positive Linear Functional L_x(f) = ⟨f(A)x, x⟩
noncomputable def spectralFunctional :
    CompactlySupportedContinuousMap ℝ ℝ →ₚ[ℝ] ℝ where
  toFun f := (Complex.re ⟪cfc f A x, x⟫_ℂ)
  map_add' f g := by
    simp only [CompactlySupportedContinuousMap.coe_add]
    rw [Pi.add_def ⇑f ⇑g, cfc_add A f g, add_apply, InnerProductSpace.add_left, Complex.add_re]
  map_smul' c f := by
    simp only [CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [Pi.smul_def c ⇑f, cfc_smul c f A]
    change (⟪(c : ℂ) • (cfc (⇑f) A) x, x⟫_ℂ).re = _
    rw [inner_smul_left _ x (c : ℂ)]
    simp
  monotone' f g hfg := by
    rw [← sub_nonneg, ← Complex.sub_re, ← inner_sub_left, ← sub_apply, ← cfc_sub g f, ← Pi.sub_def]
    let k : ℝ → ℝ := fun x => Real.sqrt ((g - f) x)
    have hk : ⇑g - ⇑f = k * k := by
      ext x
      exact (Real.mul_self_sqrt (sub_nonneg.mpr (hfg x))).symm
    rw [hk, Pi.mul_def k k, cfc_mul k k, mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_right, IsSelfAdjoint.cfc.adjoint_eq]
    simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

-- Step 2: Extract the Vector Spectral Measure
-- Applying the Riesz-Markov-Kakutani theorem yields a regular Borel measure.
noncomputable def vectorSpectralMeasure : MeasureTheory.Measure ℝ :=
  RealRMK.rieszMeasure (spectralFunctional A x)

lemma integral_eq_inner_cfc (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∫ lambda, f lambda ∂(vectorSpectralMeasure A x) = Complex.re ⟪cfc f A x, x⟫_ℂ := by
  exact RealRMK.integral_rieszMeasure (spectralFunctional A x) f

end Phase1

section Phase2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

-- Assume the measure from Phase 1 is available
variable (vectorSpectralMeasure : (H →L[ℂ] H) → H → MeasureTheory.Measure ℝ)

-- The function g must be bounded and Borel measurable.
-- We use Mathlib's bounded continuous functions or a custom bounded Borel type.
-- For this step, we assume g : ℝ → ℂ is measurable and bounded by a constant C.
variable (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ x, ‖g x‖ ≤ C)

-- Step 1: The Quadratic Form
-- Integrate the complex Borel function g with respect to the vector measure μ_x.
noncomputable def integralQuadraticForm (x : H) : ℂ :=
  ∫ lambda, g lambda ∂(vectorSpectralMeasure A x)

-- Step 2: The Polarization Identity
-- Construct the sesquilinear form B_g(x, y) by combining the quadratic forms.
noncomputable def polarizedForm (x y : H) : ℂ :=
  (1 / 4 : ℂ) * (
    integralQuadraticForm A vectorSpectralMeasure g (x + y) -
    integralQuadraticForm A vectorSpectralMeasure g (x - y) +
    Complex.I * integralQuadraticForm A vectorSpectralMeasure  g (x + Complex.I • y) -
    Complex.I * integralQuadraticForm A vectorSpectralMeasure g (x - Complex.I • y)
  )

-- Step 3: Bundle into a Continuous Linear Functional (for a fixed x)
-- To use the Riesz representation theorem, we fix x and view y ↦ conj (B_g(x, y))
-- as a continuous linear functional on H.
noncomputable def functionalForX (x : H) : H →L[ℂ] ℂ where
  toFun y := starRingEnd ℂ (polarizedForm A vectorSpectralMeasure g x y)

  -- Proof that y ↦ B_g(x, y) is conjugate-linear, so the conjugate is linear.
  map_add' y₁ y₂ := by sorry
  map_smul' c y := by sorry

  -- Proof that the functional is bounded: |B_g(x, y)| ≤ ‖g‖_∞ * ‖x‖ * ‖y‖
  -- This requires bounding the integral using the total variation of the measure.
  cont := by sorry

-- Step 4: Extract the Operator via Riesz Representation
-- Mathlib's InnerProductSpace.equivInner is the Riesz representation isomorphism.
-- It provides a unique vector z such that functionalForX(y) = ⟨y, z⟩.
-- By conjugating, this gives B_g(x, y) = ⟨z, y⟩. We define O_g(x) = z.
noncomputable def borelOperatorFun (x : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (functionalForX A vectorSpectralMeasure g x)

-- Step 5: Bundle the Operator
-- Prove that the map x ↦ O_g(x) is linear and bounded.
noncomputable def borelOperator : H →L[ℂ] H where
  toFun := borelOperatorFun A vectorSpectralMeasure g

  -- Linearity of x ↦ O_g(x) follows from the linearity of B_g(x, y) in the first argument.
  map_add' x₁ x₂ := by sorry
  map_smul' c x := by sorry

  -- Boundedness of the operator follows from the same ‖g‖_∞ bound.
  cont := by sorry

end Phase2

section Phase3

-- Assume `borelOperator A g` from Phase 2 is available
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

end Phase3
