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
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

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
  toFun f := LinearMap.mkContinuous (lift (toLinearMap₁₂ f)) ‖f‖ fun x ↦
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := LinearMap.mkContinuous₂ ((lift.equiv _ _ _ _).symm l) ‖l‖ (l.le_opNorm_tprod)
  left_inv f := by ext; simp
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    ext; simp

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
  ext; simp

section map

variable {X' X'' Y' Y'' : Type*}
variable [SeminormedAddCommGroup X'] [NormedSpace 𝕜 X']
variable [SeminormedAddCommGroup X''] [NormedSpace 𝕜 X'']
variable [SeminormedAddCommGroup Y'] [NormedSpace 𝕜 Y']
variable [SeminormedAddCommGroup Y''] [NormedSpace 𝕜 Y'']
variable (g₁ : X' →L[𝕜] X'') (g₂ : Y' →L[𝕜] Y'') (f₁ : X →L[𝕜] X') (f₂ : Y →L[𝕜] Y')

/-- Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`. -/
-- noncomputable def mapL : (X ⊗[𝕜] Y) →L[𝕜] (X' ⊗[𝕜] Y') := by
--   liftIsometry 𝕜 X Y _ <| (tprodL 𝕜).bilinearComp f
noncomputable def mapL : (X ⊗[𝕜] Y) →L[𝕜] (X' ⊗[𝕜] Y') :=
  liftIsometry 𝕜 X Y _ ((tprodL 𝕜).bilinearComp f₁ f₂)

@[simp]
theorem mapL_coe : (mapL f₁ f₂).toLinearMap = map f₁.toLinearMap f₂.toLinearMap := by
  ext; simp [mapL]

@[simp]
theorem mapL_apply (x : X ⊗[𝕜] Y) : mapL f₁ f₂ x = (map f₁.toLinearMap f₂.toLinearMap) x := by
  rfl

/-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`. -/
@[simp]
noncomputable def mapLIncl (p₁ : Submodule 𝕜 X) (p₂ : Submodule 𝕜 Y) :
    (p₁ ⊗[𝕜] p₂) →L[𝕜] X ⊗[𝕜] Y :=
  mapL p₁.subtypeL p₂.subtypeL

theorem mapL_comp : mapL (g₁ ∘L f₁) (g₂ ∘L f₂) = mapL g₁ g₂ ∘L mapL f₁ f₂ := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

theorem liftIsometry_comp_mapL (h : X' →L[𝕜] Y' →L[𝕜] F) :
    liftIsometry 𝕜 X' Y' F h ∘L mapL f₁ f₂ = liftIsometry 𝕜 X Y F (h.bilinearComp f₁ f₂) := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
theorem mapL_id : mapL (ContinuousLinearMap.id 𝕜 X) (ContinuousLinearMap.id 𝕜 Y) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
theorem mapL_one : mapL (1 : X →L[𝕜] X) (1 : Y →L[𝕜] Y) = 1 :=
  mapL_id

theorem mapL_mul (f₁₁ f₁₂ : X →L[𝕜] X) (f₂₁ f₂₂ : Y →L[𝕜] Y) :
    mapL (f₁₁ * f₁₂) (f₂₁ * f₂₂) = mapL f₁₁ f₂₁ * mapL f₁₂ f₂₂ :=
  mapL_comp _ _ _ _

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
@[simps]
noncomputable def mapLMonoidHom : (X →L[𝕜] X) × (Y →L[𝕜] Y) →* ((X ⊗[𝕜] Y) →L[𝕜] (X ⊗[𝕜] Y)) where
  toFun fg := mapL fg.1 fg.2
  map_one' := mapL_one
  map_mul' fg₁ fg₂ := mapL_mul fg₁.1 fg₂.1 fg₁.2 fg₂.2

@[simp]
protected theorem mapL_pow (f₁ : X →L[𝕜] X) (f₂ : Y →L[𝕜] Y) (n : ℕ) :
    mapL (f₁ ^ n) (f₂ ^ n) = mapL f₁ f₂ ^ n :=
  mapLMonoidHom.map_pow (f₁, f₂) n

-- -- We redeclare `ι` here, and later dependent arguments,
-- -- to avoid the `[Fintype ι]` assumption present throughout the rest of the file.
-- open Function in
-- private theorem mapL_add_smul_aux {ι : Type*}
--     {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
--     {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
--     (f : (i : ι) → E i →L[𝕜] E' i) [DecidableEq ι] (i : ι) (u : E i →L[𝕜] E' i) :
--     (fun j ↦ (update f i u j).toLinearMap) =
--       update (fun j ↦ (f j).toLinearMap) i u.toLinearMap := by
--   grind

protected theorem mapL_add_left (u v : X →L[𝕜] X') (f₂ : Y →L[𝕜] Y') :
    mapL (u + v) f₂ = mapL u f₂ + mapL v f₂ := by
  apply ContinuousLinearMap.coe_injective
  ext x y
  simp [TensorProduct.add_tmul]

protected theorem mapL_add_right (f₁ : X →L[𝕜] X') (u v : Y →L[𝕜] Y') :
    mapL f₁ (u + v) = mapL f₁ u + mapL f₁ v := by
  apply ContinuousLinearMap.coe_injective
  ext x y
  simp [TensorProduct.tmul_add]

protected theorem mapL_smul_left (c : 𝕜) (u : X →L[𝕜] X') :
    mapL (c • u) f₂ = c • mapL u f₂ := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp [TensorProduct.smul_tmul]

protected theorem mapL_smul_right (c : 𝕜) (u : Y →L[𝕜] Y') :
    mapL f₁ (c • u) = c • mapL f₁ u := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp [TensorProduct.tmul_smul]

theorem opNorm_mapL : ‖mapL f₁ f₂‖ ≤ ‖f₁‖ * ‖f₂‖ := by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x ↦ ?_
  apply le_trans (norm_eval_le_projectiveSeminorm ..) _
  have h_bound : ‖(tprodL 𝕜).bilinearComp f₁ f₂‖ ≤ ‖f₁‖ * ‖f₂‖ := by
    refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
    intro x y
    simp only [bilinearComp_apply]
    calc ‖f₁ x ⊗ₜ[𝕜] f₂ y‖
      _ ≤ ‖f₁ x‖ * ‖f₂ y‖ := projectiveSeminorm_tprod_le (f₁ x) (f₂ y)
      _ ≤ (‖f₁‖ * ‖x‖) * (‖f₂‖ * ‖y‖) :=
        mul_le_mul (le_opNorm f₁ x) (le_opNorm f₂ y) (norm_nonneg _) (by positivity)
      _ = (‖f₁‖ * ‖f₂‖) * ‖x‖ * ‖y‖ := by ring
  calc ‖(tprodL 𝕜).bilinearComp f₁ f₂‖ * ‖x‖
    _ ≤ (‖f₁‖ * ‖f₂‖) * ‖x‖ := mul_le_mul_of_nonneg_right h_bound (norm_nonneg x)

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
the family. -/
@[simps! apply_apply]
protected noncomputable def mapLBilinear :
    (X →L[𝕜] X') →L[𝕜] (Y →L[𝕜] Y') →L[𝕜] ((X ⊗[𝕜] Y) →L[𝕜] (X' ⊗[𝕜] Y')) :=
  LinearMap.mkContinuous₂ {
    toFun := (LinearMap.mk₂ 𝕜 mapL
      (fun _ _ f₂ ↦ by apply ContinuousLinearMap.coe_injective; ext; simp [TensorProduct.add_tmul])
      (fun _ _ f₂ ↦ by apply ContinuousLinearMap.coe_injective; ext; simp [TensorProduct.smul_tmul])
      (fun f₁ _ _ ↦ by apply ContinuousLinearMap.coe_injective; ext; simp [TensorProduct.tmul_add])
      (fun _ f₁ _ ↦ by apply ContinuousLinearMap.coe_injective; ext; simp [TensorProduct.tmul_smul]))
    map_add' := by
      simp only [map_add, implies_true]
    map_smul' := by
      simp only [map_smul, RingHom.id_apply, implies_true]}
  1 (fun f₁ f₂ ↦ by simp only [one_mul]; exact opNorm_mapL f₁ f₂)

-- Tactic `rewrite` failed: motive is not type correct:
--   fun _a ↦ ‖({ toFun := ?m.170, map_add' := ?m.171, map_smul' := ?m.172 } f₁) f₂‖ ≤ _a * ‖f₂‖
-- Error: Application type mismatch: The argument
--   ?m.172
-- has type
--   ∀ (m : 𝕜) (x : X →L[𝕜] X'), ?m.170 (m • x) = (RingHom.id 𝕜) m • ?m.170 x
-- but is expected to have type
--   ∀ (m : 𝕜) (x : X →L[𝕜] X'),
--     { toFun := ?m.170, map_add' := ?m.171 }.toFun (m • x) =
--       (RingHom.id 𝕜) m • { toFun := ?m.170, map_add' := ?m.171 }.toFun x
-- in the application
--   { toFun := ?m.170, map_add' := ?m.171, map_smul' := ?m.172 }

-- variable {𝕜 E E'}

-- theorem opNorm_mapLMultilinear_le : ‖mapLMultilinear 𝕜 E E'‖ ≤ 1 :=
--   MultilinearMap.mkContinuous_norm_le _ zero_le_one _

end map

end NontriviallyNormedField

end TensorProduct
