import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-! Coordinate projections and permutation isometries on actual real ℓ².
These are the projection-mass interfaces for the free-group cone argument. -/

open Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkCoordinateProjection

variable {I : Type*}
abbrev Space (I : Type*) := lp (fun _ : I => ℝ) 2

local instance (s : Set I) : DecidablePred s := Classical.decPred s

def project (s : Set I) (v : Space I) : Space I :=
  ⟨fun i => if i ∈ s then v i else 0, (lp.memℓp v).mono' (fun i => by
    by_cases hi : i ∈ s <;> simp [hi])⟩

lemma project_apply (s : Set I) (v : Space I) (i : I) :
    project s v i = if i ∈ s then v i else 0 := rfl

theorem norm_project_le (s : Set I) (v : Space I) : ‖project s v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  by_cases hi : i ∈ s <;> simp [project_apply, hi]

def projectLinear (s : Set I) : Space I →ₗ[ℝ] Space I where
  toFun := project s
  map_add' v w := by
    ext i
    change (if i ∈ s then v i + w i else 0) =
      (if i ∈ s then v i else 0) + (if i ∈ s then w i else 0)
    by_cases hi : i ∈ s <;> simp [hi]
  map_smul' r v := by
    ext i
    by_cases hi : i ∈ s <;> simp [project_apply, hi]

def projection (s : Set I) : Space I →L[ℝ] Space I :=
  (projectLinear s).mkContinuous 1 (fun v => by simpa only [one_mul] using norm_project_le s v)

@[simp] lemma projection_apply (s : Set I) (v : Space I) : projection s v = project s v := rfl

theorem project_add_compl (s : Set I) (v : Space I) : project s v + project sᶜ v = v := by
  ext i
  change project s v i + project sᶜ v i = v i
  rw [project_apply, project_apply]
  by_cases hi : i ∈ s <;> simp [hi]

theorem inner_project_disjoint (s t : Set I) (hdis : Disjoint s t) (v : Space I) :
    ⟪project s v, project t v⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  have hz : ∀ i, ⟪project s v i, project t v i⟫_ℝ = 0 := by
    intro i
    by_cases hs : i ∈ s
    · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hdis hs ht
      simp [project_apply, hs, ht, Real.inner_apply]
    · simp [project_apply, hs, Real.inner_apply]
  simp_rw [hz]
  simp

theorem norm_sq_project_add_compl (s : Set I) (v : Space I) :
    ‖project s v‖ ^ 2 + ‖project sᶜ v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := norm_add_sq_real (project s v) (project sᶜ v)
  rw [project_add_compl, inner_project_disjoint s sᶜ disjoint_compl_right] at h
  linarith

theorem project_union (s t : Set I) (hdis : Disjoint s t) (v : Space I) :
    project (s ∪ t) v = project s v + project t v := by
  ext i
  change project (s ∪ t) v i = project s v i + project t v i
  rw [project_apply, project_apply, project_apply]
  by_cases hs : i ∈ s
  · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hdis hs ht
    simp [hs, ht]
  · by_cases ht : i ∈ t <;> simp [hs, ht]

theorem norm_sq_project_union (s t : Set I) (hdis : Disjoint s t) (v : Space I) :
    ‖project (s ∪ t) v‖ ^ 2 = ‖project s v‖ ^ 2 + ‖project t v‖ ^ 2 := by
  rw [project_union s t hdis, norm_add_sq_real, inner_project_disjoint s t hdis]
  ring

theorem four_projection_mass_le (s₁ s₂ s₃ s₄ : Set I)
    (h12 : Disjoint s₁ s₂) (h13 : Disjoint s₁ s₃) (h14 : Disjoint s₁ s₄)
    (h23 : Disjoint s₂ s₃) (h24 : Disjoint s₂ s₄) (h34 : Disjoint s₃ s₄)
    (v : Space I) :
    ‖project s₁ v‖ ^ 2 + ‖project s₂ v‖ ^ 2 + ‖project s₃ v‖ ^ 2 + ‖project s₄ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hu : Disjoint (s₁ ∪ s₂) (s₃ ∪ s₄) := by
    rw [Set.disjoint_left]
    intro i hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact Set.disjoint_left.mp h13 hi hj
    · exact Set.disjoint_left.mp h14 hi hj
    · exact Set.disjoint_left.mp h23 hi hj
    · exact Set.disjoint_left.mp h24 hi hj
  have hsum := norm_sq_project_union (s₁ ∪ s₂) (s₃ ∪ s₄) hu v
  rw [norm_sq_project_union s₁ s₂ h12, norm_sq_project_union s₃ s₄ h34] at hsum
  have hb := norm_project_le ((s₁ ∪ s₂) ∪ (s₃ ∪ s₄)) v
  nlinarith [norm_nonneg (project ((s₁ ∪ s₂) ∪ (s₃ ∪ s₄)) v), norm_nonneg v]

def permute (e : I ≃ I) (v : Space I) : Space I :=
  ⟨fun i => v (e.symm i), (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    (((lp.memℓp v).summable (by norm_num)).comp_injective e.symm.injective)⟩

@[simp] lemma permute_apply (e : I ≃ I) (v : Space I) (i : I) : permute e v i = v (e.symm i) := rfl

theorem norm_permute (e : I ≃ I) (v : Space I) : ‖permute e v‖ = ‖v‖ := by
  have heq : (∑' i, ‖permute e v i‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' i, ‖v i‖ ^ (2 : ℝ≥0∞).toReal := by
    change (∑' i, ‖v (e.symm i)‖ ^ (2 : ℝ≥0∞).toReal) = _
    exact e.symm.tsum_eq (fun i => ‖v i‖ ^ (2 : ℝ≥0∞).toReal)
  rw [← lp.norm_rpow_eq_tsum (by norm_num), ← lp.norm_rpow_eq_tsum (by norm_num)] at heq
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at heq
  nlinarith [norm_nonneg (permute e v), norm_nonneg v]

def permutation (e : I ≃ I) : Space I →ₗᵢ[ℝ] Space I where
  toFun := permute e
  map_add' v w := by ext i; rfl
  map_smul' r v := by ext i; rfl
  norm_map' := norm_permute e

theorem project_permute (s : Set I) (e : I ≃ I) (v : Space I) :
    project s (permute e v) = permute e (project (e ⁻¹' s) v) := by
  ext i
  simp only [project_apply, permute_apply, Set.mem_preimage, Equiv.apply_symm_apply]

theorem norm_project_permute (s : Set I) (e : I ≃ I) (v : Space I) :
    ‖project s (permute e v)‖ = ‖project (e ⁻¹' s) v‖ := by
  rw [project_permute, norm_permute]

theorem norm_project_permute_pair (s t : Set I) (e : I ≃ I)
    (hpre : e ⁻¹' s = tᶜ) (v : Space I) :
    ‖project s (permute e v)‖ ^ 2 + ‖project t v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_project_permute, hpre]
  simpa only [add_comm] using norm_sq_project_add_compl t v

end BenchmarkCoordinateProjection

#print axioms BenchmarkCoordinateProjection.four_projection_mass_le
#print axioms BenchmarkCoordinateProjection.norm_project_permute_pair
