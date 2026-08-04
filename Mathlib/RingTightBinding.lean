import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2

variable (N : ℕ) [NeZero N]
variable (μ : ℝ) (t : ℂ)

open scoped Matrix
open Complex

def onsite (i j : Fin N) :=
  if i = j then (μ : ℂ)
  else 0

omit [NeZero N] in
theorem onsite_conjTranspose_eq_self (i j : Fin N) :  star (onsite N μ j i) = onsite N μ i j := by
  unfold onsite
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, h.symm]

def hopping_forward (i j : Fin N) :=
  if i = j + 1 then t
  else 0

def hamiltonian_fun (i j : Fin N) :=
  onsite N μ i j + hopping_forward N t i j + star (hopping_forward N t j i)

def hamiltonian := Matrix.of (hamiltonian_fun N μ t)

variable {N}

-- private lemma Fin.self_ne_add_two (hN : 2 < N) (i : Fin N) : i ≠ i + 1 + 1 := by
--   intro h
--   nth_rw 1 [← add_zero i] at h
--   rw [add_assoc] at h
--   apply add_left_cancel at h
--   apply congrArg Fin.val at h
--   simp [Fin.val_add, Nat.mod_eq_of_lt hN] at h


-- private lemma Fin.self_ne_sub_one (hN : 2 < N) (i : Fin N) : i ≠ i - 1 := by
--   intro h
--   apply add_eq_of_eq_sub at h
--   nth_rw 2 [← add_zero i] at h
--   apply add_left_cancel at h
--   apply congrArg Fin.val at h
--   rw [Fin.val_zero, Fin.val_one'] at h
--   apply Nat.one_mod_eq_zero_iff.mp at h
--   linarith


-- private lemma Fin.self_ne_add_one (hN : 2 < N) (i : Fin N) : i ≠ i + 1 := by
--   intro h
--   nth_rw 1 [← add_zero i] at h
--   apply add_left_cancel at h
--   apply congrArg Fin.val at h
--   rw [Fin.val_zero, Fin.val_one'] at h
--   replace h := h.symm
--   apply Nat.one_mod_eq_zero_iff.mp at h
--   linarith


-- private lemma Fin.sub_one_ne_add_one (hN : 2 < N) (i : Fin N) : i - 1 ≠ i + 1 := by
--   intro h
--   apply eq_add_of_sub_eq at h
--   exact Fin.self_ne_add_two hN _ h

-- private lemma Fin.add_one_ne_sub_one (hN : 2 < N) (i : Fin N) : i + 1 ≠ i - 1 := by
--   intro h
--   replace h := h.symm
--   apply Fin.sub_one_ne_add_one hN _ h

/--
This can be refined and moved to same file as Finset.sum_ite_eq
-/
lemma Finset.sum_ite_add_eq_sum_ite_sub (m n : Fin N) (f : Fin N → ℂ) :
      (∑ x, if n = x + m then f x else 0) = ∑ x, if n - m = x then f x else 0 := by
    simp_rw [sub_eq_iff_eq_add]

variable (N)


theorem isHermitian_hamiltonian : (hamiltonian N μ t).IsHermitian := by
  ext i j
  unfold hamiltonian hamiltonian_fun
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_add,
    star_star, onsite_conjTranspose_eq_self, add_comm, add_assoc]

variable (u : rootsOfUnity N ℂ)

omit [NeZero N] in
lemma u_pow : u^N = 1 := by
  ext; exact congrArg Units.val ((_root_.mem_rootsOfUnity _ _).mp u.property)

theorem inv_u : u⁻¹ = u ^ (N - 1) := by simp [pow_sub u NeZero.one_le, u_pow]
lemma norm_u : ‖(u.val : ℂ)‖ = 1 :=
  norm_eq_one_of_pow_eq_one ((mem_rootsOfUnity' N u.val).mp u.property) (NeZero.ne N)

theorem star_u : (starRingEnd ℂ) (u.val : ℂ) = (u⁻¹.val : ℂ) := by
  simp only [InvMemClass.coe_inv, Units.val_inv_eq_inv_val]
  field_simp
  rw [Complex.conj_mul', norm_u N u]
  norm_num

noncomputable def planeWaveFun (i : Fin N) : ℂ := ((u ^ i.val).val : ℂ) / √N

open lp

theorem sum_sq_norm_planeWaveFun_eq_one : ∑ x : Fin N, ‖planeWaveFun N u x‖^2 = 1 := by
  simp [planeWaveFun, norm_u, one_pow]

theorem planeWaveFun_memℓp : Memℓp (planeWaveFun N u) 2 := by
  unfold Memℓp
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    Real.rpow_ofNat]
  use 1
  suffices (∑ i, ‖planeWaveFun N u i‖ ^ 2) = 1 by
    rw [← this]
    exact hasSum_fintype _
  apply sum_sq_norm_planeWaveFun_eq_one

-- noncomputable def planeWave : ℓ²(Fin N, ℂ) := {
--   val := planeWaveFun N u
--   property := planeWaveFun_memℓp N u
-- }

noncomputable def planeWave : EuclideanSpace ℂ (Fin N) where
  ofLp i := planeWaveFun N u i

theorem isEigenvector_planeWave :
    (hamiltonian N μ t) *ᵥ planeWave N u =
    (μ + t * u.val⁻¹ + star t * u.val) • planeWave N u := by
  ext x'
  rw [Matrix.mulVec_apply]
  unfold hamiltonian hamiltonian_fun planeWave planeWaveFun dotProduct hopping_forward onsite
  simp only [Matrix.row_apply, Matrix.of_apply, add_mul, apply_ite star, star_zero, ite_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.sum_ite_add_eq_sum_ite_sub, Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul,
    Fin.val_sub, Fin.val_add, Fin.val_one']
  have pow_mod : ∀ m : ℕ, u ^ m = u ^ (m % N : ℕ) := by
    intro m
    obtain ⟨uv, hu⟩ := u
    simp only [SubmonoidClass.mk_pow, Subtype.mk.injEq]
    exact pow_eq_pow_mod m hu
  simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, ← pow_mod, RCLike.star_def,
    Nat.add_mod_mod, Units.val_inv_eq_inv_val]
  rcases N with _ | N | N
  · exact absurd rfl (NeZero.ne 0)
  · norm_num
    have hu : u = 1 := by simpa using u.property
    simp [hu]
  · norm_num; norm_cast; simp [inv_u]; ring

open lp

-- 1. State that the set of vectors is orthonormal
theorem orthonormal_planeWaves : Orthonormal ℂ (planeWave N) := by
  constructor
  · intro u
    rw [← abs_one, ← abs_norm, ← sq_eq_sq_iff_abs_eq_abs, one_pow]
    simp [norm]
    simp [normSq_eq_norm_sq]
    simp only [planeWave]
    simp [sum_sq_norm_planeWaveFun_eq_one N u]
  · intro u u' h_ne
    unfold planeWave planeWaveFun
    simp [PiLp.inner_apply]
    simp only [star_u, InvMemClass.coe_inv, Units.val_inv_eq_inv_val, inv_pow]
    simp [div_mul_eq_mul_div, mul_div, div_div, ← Finset.sum_div, div_eq_zero_iff]
    have h_ne' : (u'.val : ℂ)/(u.val : ℂ) ≠ 1:= by
      simp only [ne_eq]
      apply div_ne_one_of_ne
      intro h_eq
      rw [Units.val_inj, Subtype.val_inj] at h_eq
      exact h_ne h_eq.symm
    simp [← div_eq_mul_inv, ← div_pow]
    simp [Fin.sum_univ_eq_sum_range, geom_sum_eq h_ne']
    simp [div_pow]
    norm_cast
    simp [u_pow]

noncomputable instance : Fintype (rootsOfUnity N ℂ) where
  elems := Finset.univ.image fun (i : Fin N) =>
    let val := exp (2 * Real.pi * I * (i.val / N))
    let unit_val := Units.mk0 val (exp_ne_zero _)
    ⟨unit_val, (Complex.mem_rootsOfUnity N unit_val).mpr
      ⟨i, i.isLt, by simp only [unit_val, val, Units.val_mk0]⟩⟩
  complete := by
    intro ⟨x, hx⟩
    obtain ⟨i, h_lt, h_eq⟩ := (Complex.mem_rootsOfUnity N x).mp hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    use ⟨i, h_lt⟩
    ext
    exact h_eq


-- 2. Construct the complete orthonormal basis using the orthonormality proof
noncomputable def planeWaveBasis :
    Module.Basis (rootsOfUnity N ℂ) ℂ (EuclideanSpace ℂ (Fin N)) := by
  apply basisOfOrthonormalOfCardEqFinrank (orthonormal_planeWaves N) (by
    rw [Fintype.card_eq_nat_card, Complex.card_rootsOfUnity]; simp)


-- 1. State that the set of vectors is orthonormal
theorem orthonormal_planeWavesBasis : Orthonormal ℂ (planeWaveBasis N) := by
  unfold planeWaveBasis
  simp only [coe_basisOfOrthonormalOfCardEqFinrank]
  exact orthonormal_planeWaves N

open Module

noncomputable def planeWaveOrthonormalBasis :
    OrthonormalBasis (rootsOfUnity N ℂ) ℂ (EuclideanSpace ℂ (Fin N)) :=
  Basis.toOrthonormalBasis (planeWaveBasis N) (orthonormal_planeWavesBasis N)
