import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

section problem1

-- Define a concrete matrix
def A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1;
     1, 2]

-- Define the known eigenvalue and eigenvector
def λ : ℝ := 3
def v : Fin 2 → ℝ := ![1, 1]

-- 1. Prove the eigenvector equation: A * v = λ * v
lemma is_eigenvalue_eq : A *ᵥ v = λ • v := by
  ext i
  -- fin_cases expands the Fin 2 index into explicit cases for row 0 and row 1.
  -- norm_num computes the matrix multiplication and scalar arithmetic.
  fin_cases i <;> norm_num

-- 2. Prove the eigenvector is non-zero
lemma v_ne_zero : v ≠ 0 := by
  intro h
  -- Extract the first element of the vector to show a contradiction
  have h0 : v 0 = 0 := congrFun h 0
  revert h0
  norm_num

end problem1

section problem2

def A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
def P : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, 1]
def lambda : Fin 2 → ℝ := ![3, 1]

-- 1. Upgrade P's columns to a Basis (proving completeness)
lemma P_is_invertible : P.det ≠ 0 := by norm_num
noncomputable def P_basis : Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  Matrix.toBasis P (Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr P_is_invertible))

-- 2. Prove they form the eigensystem for A (proving validity)
lemma complete_eigensystem : 
    Module.End.HasEigenbasis (Matrix.toLin' A) P_basis lambda := by
  intro i
  -- Unfold the basis into matrix vector multiplication
  simp only [P_basis, Matrix.toBasis_apply, Matrix.toLin'_apply, Matrix.mulVec]
  fin_cases i <;> ext j <;> fin_cases j <;> norm_num

end problem2