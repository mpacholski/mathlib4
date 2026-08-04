import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Matrix.Hermitian



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

lemma norm_u_eq_one : ‖(u.val : ℂ)‖ = 1 :=
  norm_eq_one_of_pow_eq_one ((mem_rootsOfUnity' N u.val).mp (SetLike.coe_mem u)) (NeZero.ne N)

noncomputable def planeWaveFun (i : Fin N) : ℂ := ((u ^ i.val).val : ℂ) / √N

open lp

theorem sum_sq_norm_planeWaveFun_eq_one : ∑ x : Fin N, ‖planeWaveFun N u x‖^2 = 1 := by
  simp [planeWaveFun, norm_u_eq_one, one_pow]

theorem planeWaveFun_memℓp : Memℓp (planeWaveFun N u) 2 := by
  unfold Memℓp
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    Real.rpow_ofNat]
  use 1
  suffices (∑ i, ‖planeWaveFun N u i‖ ^ 2) = 1 by
    rw [← this]
    exact hasSum_fintype _
  apply sum_sq_norm_planeWaveFun_eq_one

noncomputable def planeWave : ℓ²(Fin N, ℂ) := {
  val := planeWaveFun N u
  property := planeWaveFun_memℓp N u
}

theorem pow_sub_one

theorem isEigenvector_planeWave :
    (hamiltonian N μ t) *ᵥ planeWave N u =
    (μ + t * u.val⁻¹ + star t * u.val) • planeWave N u := by
  -- obtain ⟨u, hu⟩ := u
  -- simp only [mem_rootsOfUnity] at hu
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
    simp
    exact pow_eq_pow_mod m hu
  simp [← pow_mod]
  rcases N with _ | N | N
  · exact absurd rfl (NeZero.ne 0)
  · obtain ⟨uv, hu⟩ := u
    norm_num at hu
    norm_num
    simp [hu]
  · simp [← mul_div_assoc, ← add_div]
    apply (div_eq_iff _).mpr
    simp [div_mul]
    have : (√(N + 1 + 1) : ℂ) ≠ 0 := by
      sorry
    rw [(div_self_eq_one₀).mpr this, div_one]
    nth_rw 2 [← sub_add_cancel ]



    sorry
    norm_num
    obtain ⟨u, hu⟩ := u
    -- simp at hu
    -- simp [← pow_add]
    -- have hN' : 1 < N := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨NeZero.ne N, hN⟩
    -- simp [Nat.mod_eq_of_lt hN', pow_add]
    -- have : u ^ (N - 1) = u^N / u := by
      -- apply?
    -- rw []
    -- rw [Nat.mod_eq_of_lt hN', Nat.cast_add, Nat.cast_sub (Nat.one_le_of_lt hN'), Nat.cast_one]
    simp [mul_add, exp_add, sub_eq_add_neg, hk,]
    simp [mul_assoc, mul_comm]
    ring

open lp

example (x y : ℝ) (h : x = y) : x^2 = y^2 := by
  exact (sq_eq_sq_iff_abs_eq_abs x y).mpr (congrArg abs h)

example (a b c d : ℂ) (h : a = b) (h' : c = d) : (a/c = b/d) := by
  rw [h, h']




-- 1. State that the set of vectors is orthonormal
theorem orthonormal_planeWaves : Orthonormal ℂ (planeWave N) := by
  constructor
  · intro k
    rw [← abs_one, ← abs_norm, ← sq_eq_sq_iff_abs_eq_abs, one_pow]
    simp [norm]
    simp [normSq_eq_norm_sq]
    simp [DFunLike.coe, planeWave]
    rw [sum_sq_norm_planeWaveFun_eq_one N k]
    norm_num
  · intro k k' h_ne
    obtain ⟨k, hk⟩ := k; simp only [us, Set.mem_ofPred] at hk
    obtain ⟨k', hk'⟩ := k'; simp only [us, Set.mem_ofPred] at hk'
    simp only [ne_eq, Subtype.mk.injEq] at h_ne
    unfold planeWave planeWaveFun
    simp only [inner_eq_tsum, RCLike.inner_apply, map_div₀, ← exp_conj, map_mul, conj_I,
      conj_ofReal, neg_mul, map_natCast, ← mul_div_assoc, div_mul_eq_mul_div, ← exp_add, div_div,
      ← ofReal_mul, Nat.cast_nonneg, Real.mul_self_sqrt, ofReal_natCast, tsum_fintype]
    simp_rw [← mul_neg, ← neg_mul_comm, ← mul_neg]
    simp_rw [← add_mul, ← mul_add, ← sub_eq_add_neg]
    have (x : ℕ) : exp (I * (k' - k) * x) = exp (I * (k' - k))^x := by
      nth_rw 1 [mul_comm]; simp [exp_nat_mul]
    simp_rw [this, ← Finset.sum_div]

    have hkk' : exp (I * (k - k') * N) = 1 := by
      simp_rw [mul_sub, sub_mul, sub_eq_add_neg, exp_add, exp_neg, hk, hk']
      norm_num
    sorry

-- 2. Construct the complete orthonormal basis using the orthonormality proof
noncomputable def planeWaveBasis : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  basisOfOrthonormalOfCardEqFinrank (orthonormal_planeWaves N) (by simp)


open Complex

example (N : ℝ) (h : N ≠ 0) : N / N = 1 := by
  exact (div_eq_one_iff_eq h).mpr rfl
