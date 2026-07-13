module

import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear


/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a normed field and `X` and `Y` be normed `𝕜`-vector spaces.
We define a seminorm on `X ⊗[𝕜] Y`, which we call the "projective seminorm".
For `t` an element of `X ⊗[𝕜] Y`, its projective seminorm is the
infimum over all expressions of `t` as `∑ j, xⱼ ⊗ₜ[𝕜] yⱼ` (with the `(xⱼ,yⱼ)` ∈ `X × Y`)
of `∑ j, ‖xⱼ‖ * ‖yⱼ‖ `.

In particular, every norm `‖.‖` on `X ⨂[𝕜] Y` satisfying `‖x ⊗ₜ[𝕜] y‖ ≤ ‖x‖ * ‖y‖`
for every `(x,y)` in `X × Y` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `X ⨂[𝕜] Y`.
* `PiTensorProduct.liftEquiv`: The bijection between `X →L[𝕜] Y →L[𝕜] F`
  and `(X ⊗[𝕜] Y) →L[𝕜] F`, as a continuous linear equivalence.
* `PiTensorProduct.liftIsometry`: The bijection between `X →L[𝕜] Y →L[𝕜] F`
  and `(X ⊗[𝕜] Y) →L[𝕜] F`,, as an isometric linear equivalence.
* `PiTensorProduct.tprodL`: The canonical continuous bilinear map from `X × Y`
  to `X ⊗[𝕜] Y`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous bilinear map on
  `X × Y` and `x` is in `X ⊗[𝕜] Y`, then `‖lift (toLinearMap₁₂ f) x‖ ≤ ‖f‖ * ‖x‖`.

## TODO
* If the base field is `ℝ` or `ℂ` (or more generally if the injection of `Eᵢ` into its bidual is
  an isometry for every `i`), then we have `projectiveSeminorm ⨂ₜ[𝕜] i, mᵢ = Π i, ‖mᵢ‖`.
* If all `Eᵢ` are separated and satisfy `SeparatingDual`, then the seminorm on
  `⨂[𝕜] i, Eᵢ` is a norm.
* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.

-/

-- @[expose] public section

variable {𝕜 X Y: Type*}
variable [SeminormedAddCommGroup X]
variable [SeminormedAddCommGroup Y]

open scoped TensorProduct

namespace TensorProduct

section NormedField

variable [NormedField 𝕜]

/-- A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to prove the
properties of `projectiveSeminorm`. -/
def projectiveSeminormAux : FreeAddMonoid (X × Y) → ℝ :=
  fun p ↦ (p.toList.map (fun p ↦ ‖p.1‖ * ‖p.2‖)).sum

theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (X × Y)) :
    0 ≤ projectiveSeminormAux p := by
  refine List.sum_nonneg fun a ↦ ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x y _ rfl
  positivity

theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (X × Y)) :
    projectiveSeminormAux (p + q) ≤ projectiveSeminormAux p + projectiveSeminormAux q := by
  simp only [projectiveSeminormAux, FreeAddMonoid.toList_add, List.map_append, List.sum_append,
    Std.le_refl]

variable [NormedSpace 𝕜 X]

theorem projectiveSeminormAux_smul (p : FreeAddMonoid (X × Y)) (a : 𝕜) :
    projectiveSeminormAux (p.map (fun (y : X × Y) ↦ (a • y.1, y.2))) =
    ‖a‖ * projectiveSeminormAux p := by
  simp only [projectiveSeminormAux, FreeAddMonoid.toList_map, List.map_map, Function.comp_def]
  simp_rw [norm_smul, mul_assoc]
  rw [List.sum_map_mul_left]

variable [NormedSpace 𝕜 Y]

theorem bddBelow_projectiveSemiNormAux (x : X ⊗[𝕜] Y) :
    BddBelow (Set.range (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) :=
  ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩

noncomputable instance : Norm (X ⊗[𝕜] Y) :=
  ⟨fun x ↦ iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val)⟩

theorem norm_def (x : X ⊗[𝕜] Y) :
    ‖x‖ = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val) := rfl

theorem projectiveSeminorm_zero : ‖(0 : X ⊗[𝕜] Y)‖ = 0 :=
  le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p ↦ projectiveSeminormAux_nonneg p.val))

theorem projectiveSeminorm_add_le (x y : X ⊗[𝕜] Y) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  le_ciInf_add_ciInf (fun p q ↦ ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))

theorem projectiveSeminorm_smul_le (a : 𝕜) (x : X ⊗[𝕜] Y) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p ↦ ?_
  simpa [projectiveSeminormAux_smul] using
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul_left p.2 a⟩ (le_refl _)

/-- The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ` to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`. -/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (X ⊗[𝕜] Y) := .ofSMulLE
    _ projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le

noncomputable instance : SeminormedAddCommGroup (X ⊗[𝕜] Y) :=
  fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

noncomputable instance : NormedSpace 𝕜 (X ⊗[𝕜] Y) := ⟨projectiveSeminorm_smul_le⟩

theorem projectiveSeminorm_tprod_le (x : X) (y : Y) :
    projectiveSeminorm (x ⊗ₜ[𝕜] y) ≤ ‖x‖*‖y‖ := by
  convert! ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨FreeAddMonoid.of (x, y), ?_⟩
  · simp [projectiveSeminormAux]
  · simp [mem_lifts_iff]

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

open ContinuousLinearMap

example {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : X →L[𝕜] Y →L[𝕜] G) : X →ₗ[𝕜] Y →ₗ[𝕜] G :=
  (coeLM 𝕜 ∘ₗ f.toLinearMap)

theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : X →L[𝕜] Y →L[𝕜] G) (x : X ⊗[𝕜] Y) :
    ‖lift (toLinearMap₁₂ f) x‖ ≤ ‖f‖ * ‖x‖ := by
  rw [norm_def, mul_comm, Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ ↦ ?_
  rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
  refine List.Forall₂.sum_le_sum ?_
  simpa [←mul_assoc, mul_comm] using fun x y _ ↦
    ((f x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (f.le_opNorm x) (norm_nonneg y))

lemma _root_.ContinuousLinearMap.le_opNorm_tprod {𝕜 X Y F : Type*}
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (l : X ⊗[𝕜] Y →L[𝕜] F) (x : X) (y : Y) :
    ‖l (x ⊗ₜ[𝕜] y)‖ ≤ ‖l‖ * ‖x‖ * ‖y‖ := by
    calc
      ‖l (x ⊗ₜ[𝕜] y)‖ ≤ ‖l‖ * projectiveSeminorm (x ⊗ₜ[𝕜] y) := l.le_opNorm (x ⊗ₜ[𝕜] y)
      _ ≤ ‖l‖ * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left (projectiveSeminorm_tprod_le x y)
        (norm_nonneg l)
      _ = ‖l‖ * ‖x‖ * ‖y‖ := by rw [mul_assoc]

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 X Y F)

/-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`.
-/
@[simps]
noncomputable def liftEquiv : (X →L[𝕜] Y →L[𝕜] F) ≃ₗ[𝕜] X ⊗[𝕜] Y →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift (toLinearMap₁₂ f)) ‖f‖ (norm_eval_le_projectiveSeminorm f)
  invFun l := LinearMap.mkContinuous₂ ((lift.equiv _ X Y F).symm l) ‖l‖ l.le_opNorm_tprod
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  left_inv f := by ext; simp
  right_inv l := by
    ext x;
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]


/-- For a normed space `F`, we have constructed in `PiTensorProduct.liftEquiv` the canonical
linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
(induced by `PiTensorProduct.lift`). Here we give the upgrade of this equivalence to
an isometric linear equivalence; in particular, it is a continuous linear equivalence. -/
noncomputable def liftIsometry : (X →L[𝕜] Y →L[𝕜] F) ≃ₗᵢ[𝕜] X ⊗[𝕜] Y →L[𝕜] F :=
  LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 X Y F)
  (fun f ↦ LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
  (fun f ↦ by
      rw [liftEquiv_symm_apply]
      exact LinearMap.mkContinuous₂_norm_le ((lift.equiv (RingHom.id 𝕜) X Y F).symm ↑f)
        (norm_nonneg f) (f.le_opNorm_tprod))

variable {𝕜 X Y F}

@[simp]
theorem liftIsometry_apply_apply (f : X →L[𝕜] Y →L[𝕜] F) (x : X ⊗[𝕜] Y) :
    liftIsometry 𝕜 X Y F f x = lift (toLinearMap₁₂ f) x := by
  simp [LinearIsometryEquiv.ofBounds, liftIsometry]

variable (𝕜) in
/-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`. -/
@[simps!]
noncomputable def tprodL :  X →L[𝕜] Y →L[𝕜] (X ⊗[𝕜] Y) :=
  (liftIsometry 𝕜 X Y _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]
theorem tprodL_coe : toLinearMap₁₂ (tprodL 𝕜) = TensorProduct.mk 𝕜 X Y := by
  ext; simp

-- @[simp]
theorem liftIsometry_symm_apply (l : (X ⊗[𝕜] Y) →L[𝕜] F) :
    (liftIsometry 𝕜 X Y F).symm l = ((ContinuousLinearMap.compL 𝕜 _ _ _ l)).comp (tprodL 𝕜)
    := by
  rfl

@[simp]
theorem liftIsometry_tprodL :
  liftIsometry 𝕜 X Y _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (X ⊗[𝕜] Y) := by
  apply ContinuousLinearMap.coe_injective
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]


end NontriviallyNormedField

end TensorProduct
