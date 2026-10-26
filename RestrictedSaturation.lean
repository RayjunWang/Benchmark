import RestrictedAction
import RestrictedSupport

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def innerInterval : Set ℝ := Icc (-(3 : ℝ) * Real.log 2 / 4) (-Real.log 2 / 4)

theorem innerInterval_subset : innerInterval ⊆ baseInterval := by
  intro t ht
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor <;> dsimp [innerInterval] at ht <;> linarith [ht.1, ht.2]

theorem baseMeasure_innerInterval_pos : 0 < baseMeasure innerInterval := by
  have hvol : 0 < volume innerInterval := by
    rw [innerInterval, Real.volume_Icc]
    apply ENNReal.ofReal_pos.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hle := volume_restrict_le_baseMeasure innerInterval
  rw [Measure.restrict_apply (show MeasurableSet innerInterval from measurableSet_Icc),
    Set.inter_eq_left.mpr innerInterval_subset] at hle
  exact hvol.trans_le hle

theorem tailProbability_ae_frequently_innerInterval :
    ∀ᵐ x ∂tailProbability, ∃ᶠ n in atTop, x n ∈ innerInterval := by
  let A : ℕ → Set RealSequences := fun n => {x | x n ∈ innerInterval}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurable_pi_apply n) (show MeasurableSet innerInterval from measurableSet_Icc)
  have hA (n : ℕ) : tailProbability (A n) = baseMeasure innerInterval := by
    have hm : tailProbability.map (fun x => x n) = baseMeasure :=
      Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) n
    change tailProbability ((fun x : RealSequences => x n) ⁻¹' innerInterval) = _
    rw [← Measure.map_apply (measurable_pi_apply n)
      (show MeasurableSet innerInterval from measurableSet_Icc), hm]
  have hi : ProbabilityTheory.iIndepSet A tailProbability := by
    apply (ProbabilityTheory.iIndepSet_iff_meas_biInter hAm).mpr
    intro s
    have he : (⋂ i ∈ s, A i) = Set.pi s (fun _ => innerInterval) := by
      ext x
      simp [A, Set.mem_pi]
    rw [he]
    change Measure.infinitePi (fun _ : ℕ => baseMeasure)
      (Set.pi s (fun _ => innerInterval)) = _
    rw [Measure.infinitePi_pi (fun _ : ℕ => baseMeasure)
      (fun _ _ => show MeasurableSet innerInterval from measurableSet_Icc)]
    exact Finset.prod_congr rfl (fun i _ => (hA i).symm)
  have hsum : (∑' n, tailProbability (A n)) = ∞ := by
    simp_rw [hA]
    exact ENNReal.tsum_const_eq_top_of_ne_zero baseMeasure_innerInterval_pos.ne'
  have hprob := ProbabilityTheory.measure_limsup_eq_one hAm hi hsum
  have hae : ∀ᵐ x ∂tailProbability, x ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hAm)).mpr hprob
  filter_upwards [hae] with x hx
  exact mem_limsup_iff_frequently_mem.mp hx

theorem measurable_frequently_innerInterval :
    MeasurableSet {x : RealSequences | ∃ᶠ n in atTop, x n ∈ innerInterval} := by
  have he : {x : RealSequences | ∃ᶠ n in atTop, x n ∈ innerInterval} =
      limsup (fun n => {x : RealSequences | x n ∈ innerInterval}) atTop := by
    ext x
    exact (mem_limsup_iff_frequently_mem (a := x)
      (s := fun n => {y : RealSequences | y n ∈ innerInterval}) (𝓕 := atTop)).symm
  rw [he]
  exact MeasurableSet.measurableSet_limsup (fun n =>
    (measurable_pi_apply n) (show MeasurableSet innerInterval from measurableSet_Icc))

theorem stageMeasure_ae_frequently_innerInterval (n : ℕ) :
    ∀ᵐ x ∂stageMeasure n, ∃ᶠ k in atTop, x k ∈ innerInterval := by
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    measurable_frequently_innerInterval).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((headTailEquiv n).symm.measurable measurable_frequently_innerInterval)).mpr
  apply ae_of_all
  intro head
  filter_upwards [tailProbability_ae_frequently_innerInterval] with tail ht
  rw [frequently_atTop] at ht ⊢
  intro N
  obtain ⟨r, hr, hri⟩ := ht N
  refine ⟨n + r, by omega, ?_⟩
  simpa only [headTailEquiv_symm_tail] using hri

theorem restrictedProductMeasure_ae_frequently_innerInterval :
    ∀ᵐ x ∂restrictedProductMeasure, ∃ᶠ n in atTop, x n ∈ innerInterval := by
  rw [ae_iff]
  change restrictedProductStages.limit {x | ¬ ∃ᶠ n in atTop, x n ∈ innerInterval} = 0
  have hbad : MeasurableSet {x : RealSequences | ¬ ∃ᶠ n in atTop, x n ∈ innerInterval} :=
    measurable_frequently_innerInterval.compl
  rw [restrictedProductStages.limit_apply _ hbad]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  exact stageMeasure_ae_frequently_innerInterval n

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.restrictedProductMeasure_ae_frequently_innerInterval
