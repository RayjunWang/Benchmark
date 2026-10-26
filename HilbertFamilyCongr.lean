import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Actual coordinatewise unitary equivalences of countable Hilbert sums. -/

open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {I : Type*} {H G : I → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

def hilbertFamilyMap (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) (x : lp H 2) : lp G 2 :=
  ⟨fun i => e i (x i), by
    apply memℓp_gen
    simpa only [LinearIsometryEquiv.norm_map] using
      (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)⟩

theorem hilbertFamilyMap_norm (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) (x : lp H 2) :
    ‖hilbertFamilyMap e x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  apply tsum_congr
  intro i
  simp only [hilbertFamilyMap, LinearIsometryEquiv.norm_map]

def hilbertFamilyCongr (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) : lp H 2 ≃ₗᵢ[ℂ] lp G 2 where
  toFun := hilbertFamilyMap e
  invFun := hilbertFamilyMap (fun i => (e i).symm)
  left_inv x := by
    apply lp.ext
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    apply lp.ext
    funext i
    exact (e i).apply_symm_apply (x i)
  map_add' x y := by
    apply lp.ext
    funext i
    exact (e i).map_add (x i) (y i)
  map_smul' c x := by
    apply lp.ext
    funext i
    exact (e i).map_smul c (x i)
  norm_map' := hilbertFamilyMap_norm e

theorem hilbertFamilyCongr_single [DecidableEq I]
    (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) (i : I) (x : H i) :
    hilbertFamilyCongr e (lp.single 2 i x) = lp.single 2 i (e i x) := by
  apply lp.ext
  funext j
  by_cases hj : j = i
  · subst j
    simp [hilbertFamilyCongr, hilbertFamilyMap]
  · simp [hilbertFamilyCongr, hilbertFamilyMap, lp.single_apply, hj]

end
end MeasureUnitary

#print axioms MeasureUnitary.hilbertFamilyCongr
