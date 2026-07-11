-- module

import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Seminorm


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

-- noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
--   fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

-- noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) := ⟨projectiveSeminorm_smul_le⟩

-- @[deprecated norm_def (since := "2026-06-10")]
-- theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
--     projectiveSeminorm x = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1) := rfl

-- theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
--     projectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ := by
--   convert! ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨FreeAddMonoid.of ((1 : 𝕜), m), ?_⟩
--   · simp [projectiveSeminormAux]
--   · simp [mem_lifts_iff]

-- end NormedField

-- section NontriviallyNormedField

-- variable [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

-- theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
--     [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E i) :
--     ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * ‖x‖ := by
--   rw [norm_def, mul_comm, Real.iInf_mul_of_nonneg (norm_nonneg _)]
--   refine le_ciInf fun ⟨p, hp⟩ ↦ ?_
--   rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
--   grw [norm_multiset_sum_le]
--   simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
--   refine List.Forall₂.sum_le_sum ?_
--   simpa [norm_smul, ← mul_assoc, mul_comm ‖f‖ _] using
--     fun a m _ ↦ mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

-- variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

-- variable (𝕜 E F)

-- /-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
-- induced by `PiTensorProduct.lift`, for every normed space `F`.
-- -/
-- @[simps]
-- noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
--   toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x ↦
--     norm_eval_le_projectiveSeminorm f x
--   map_add' f g := by ext; simp
--   map_smul' a f := by ext; simp
--   invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x ↦
--     ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
--   left_inv f := by ext; simp
--   right_inv l := by
--     rw [← ContinuousLinearMap.coe_inj]
--     ext; simp

-- /-- For a normed space `F`, we have constructed in `PiTensorProduct.liftEquiv` the canonical
-- linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
-- (induced by `PiTensorProduct.lift`). Here we give the upgrade of this equivalence to
-- an isometric linear equivalence; in particular, it is a continuous linear equivalence. -/
-- noncomputable def liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
--   LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 E F)
--   (fun f ↦ LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
--   (fun f ↦ by
--       rw [liftEquiv_symm_apply]
--       exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

-- variable {𝕜 E F}

-- @[simp]
-- theorem liftIsometry_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
--     liftIsometry 𝕜 E F f x = lift f.toMultilinearMap x := by
--   simp [LinearIsometryEquiv.ofBounds, liftIsometry]

-- variable (𝕜) in
-- /-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`. -/
-- @[simps! toFun]
-- noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
--   (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

-- @[simp]
-- theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
--   ext; simp

-- @[simp]
-- theorem liftIsometry_symm_apply (l : (⨂[𝕜] i, E i) →L[𝕜] F) :
--     (liftIsometry 𝕜 E F).symm l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
--   rfl

-- @[simp]
-- theorem liftIsometry_tprodL :
--     liftIsometry 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
--   ext; simp

-- section map

-- variable {E' E'' : ι → Type*}
-- variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
-- variable [∀ i, SeminormedAddCommGroup (E'' i)] [∀ i, NormedSpace 𝕜 (E'' i)]
-- variable (g : Π i, E' i →L[𝕜] E'' i) (f : Π i, E i →L[𝕜] E' i)

-- /-- Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
-- Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
-- `f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
-- `⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`. -/
-- noncomputable def mapL : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
--   liftIsometry 𝕜 E _ <| (tprodL 𝕜).compContinuousLinearMap f

-- @[simp]
-- theorem mapL_coe : (mapL f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := by
--   ext; simp [mapL]

-- @[simp]
-- theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i ↦ (f i).toLinearMap) x := by
--   rfl

-- /-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
-- This is the continuous version of `PiTensorProduct.mapIncl`. -/
-- @[simp]
-- noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →L[𝕜] ⨂[𝕜] i, E i :=
--   mapL fun (i : ι) ↦ (p i).subtypeL

-- theorem mapL_comp : mapL (fun (i : ι) ↦ g i ∘L f i) = mapL g ∘L mapL f := by
--   apply ContinuousLinearMap.coe_injective
--   ext; simp

-- theorem liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
--     liftIsometry 𝕜 E' F h ∘L mapL f = liftIsometry 𝕜 E F (h.compContinuousLinearMap f) := by
--   apply ContinuousLinearMap.coe_injective
--   ext; simp

-- @[simp]
-- theorem mapL_id : mapL (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
--   apply ContinuousLinearMap.coe_injective
--   ext; simp

-- @[simp]
-- theorem mapL_one : mapL (fun (i : ι) ↦ (1 : E i →L[𝕜] E i)) = 1 :=
--   mapL_id

-- theorem mapL_mul (f₁ f₂ : Π i, E i →L[𝕜] E i) :
--     mapL (fun i ↦ f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
--   mapL_comp f₁ f₂

-- /-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
-- @[simps]
-- noncomputable def mapLMonoidHom : (Π i, E i →L[𝕜] E i) →* ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E i) where
--   toFun := mapL
--   map_one' := mapL_one
--   map_mul' := mapL_mul

-- @[simp]
-- protected theorem mapL_pow (f : Π i, E i →L[𝕜] E i) (n : ℕ) :
--     mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom f n

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

-- open Function in
-- protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i →L[𝕜] E' i) :
--     mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
--   ext
--   simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]

-- open Function in
-- protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i →L[𝕜] E' i) :
--     mapL (update f i (c • u)) = c • mapL (update f i u) := by
--   ext
--   simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]

-- theorem opNorm_mapL : ‖mapL f‖ ≤ ∏ i, ‖f i‖ := by
--   refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x ↦ ?_
--   apply le_trans (norm_eval_le_projectiveSeminorm ..) (mul_le_mul_of_nonneg_right _ (norm_nonneg x))
--   refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m ↦ ?_
--   apply le_trans (projectiveSeminorm_tprod_le fun i ↦ f i (m i))
--   rw [← Finset.prod_mul_distrib]
--   gcongr
--   exact ContinuousLinearMap.le_opNorm _ _

-- variable (𝕜 E E')

-- /-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
-- the family. -/
-- @[simps! toFun_apply]
-- noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E i →L[𝕜] E' i)
--     ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i) :=
--   MultilinearMap.mkContinuous
--   { toFun := mapL
--     map_update_smul' := fun _ _ _ _ ↦ PiTensorProduct.mapL_smul _ _ _ _
--     map_update_add' := fun _ _ _ _ ↦ PiTensorProduct.mapL_add _ _ _ _ }
--   1 (fun f ↦ by rw [one_mul]; exact opNorm_mapL f)

-- variable {𝕜 E E'}

-- theorem opNorm_mapLMultilinear_le : ‖mapLMultilinear 𝕜 E E'‖ ≤ 1 :=
--   MultilinearMap.mkContinuous_norm_le _ zero_le_one _

-- end map

-- end NontriviallyNormedField

-- end TensorProduct
