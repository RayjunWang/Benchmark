import RestrictedCorrection
import RestrictedZeroOne

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem ae_exists_zeroSum_shift_to_base :
    ∀ᵐ x ∂restrictedProductMeasure,
      ∃ q : rationalZeroSumGroup, rationalTranslation q x ∈ stageSet 0 := by
  filter_upwards [restrictedProductStages.ae_mem_union,
    restrictedProductMeasure_ae_frequently_innerInterval] with x hx hf
  exact exists_zeroSum_shift_to_base x hx hf

theorem rational_saturation_conull :
    restrictedProductMeasure (⋃ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' stageSet 0)ᶜ = 0 := by
  have he : ∀ᵐ x ∂restrictedProductMeasure,
      x ∈ ⋃ q : rationalZeroSumGroup, (rationalTranslation q) ⁻¹' stageSet 0 := by
    simpa only [mem_iUnion, mem_preimage] using ae_exists_zeroSum_shift_to_base
  exact he

theorem null_of_invariant_and_base_null (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E)
    (hbase : tailProbability E = 0) : restrictedProductMeasure E = 0 := by
  have hzero : restrictedProductMeasure (E ∩ stageSet 0) = 0 := by
    rw [← Measure.restrict_apply hE, restrictedProductMeasure_restrict 0,
      stageMeasure_zero, hbase]
  have hS : ∀ᵐ x ∂restrictedProductMeasure, x ∈ stageSet 0 → x ∉ E := by
    rw [ae_iff]
    have he : {x | ¬ (x ∈ stageSet 0 → x ∉ E)} = E ∩ stageSet 0 := by
      ext x
      simp only [mem_setOf_eq, _root_.not_imp, not_not, mem_inter_iff, and_comm]
    rw [he]
    exact hzero
  have hq (q : rationalZeroSumGroup) : ∀ᵐ x ∂restrictedProductMeasure,
      rationalTranslation q x ∈ stageSet 0 → x ∉ E := by
    have hpull := (measurePreserving_rationalTranslation q).quasiMeasurePreserving.ae hS
    filter_upwards [hpull, (hinv q).mem_iff] with x hx he
    intro hs hxe
    exact hx hs (he.mpr hxe)
  have hall : ∀ᵐ x ∂restrictedProductMeasure,
      ∀ q : rationalZeroSumGroup, rationalTranslation q x ∈ stageSet 0 → x ∉ E :=
    ae_all_iff.mpr hq
  have hnot : ∀ᵐ x ∂restrictedProductMeasure, x ∉ E := by
    filter_upwards [hall, ae_exists_zeroSum_shift_to_base] with x hx hex
    obtain ⟨q, hq⟩ := hex
    exact hx q hq
  simpa only [ae_iff, not_not] using hnot

theorem null_or_conull_of_invariant_and_base_zero_one
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E)
    (hbase : tailProbability E = 0 ∨ tailProbability Eᶜ = 0) :
    restrictedProductMeasure E = 0 ∨ restrictedProductMeasure Eᶜ = 0 := by
  rcases hbase with h0 | h1
  · exact Or.inl (null_of_invariant_and_base_null E hE hinv h0)
  · apply Or.inr
    apply null_of_invariant_and_base_null Eᶜ hE.compl _ h1
    intro q
    simpa only [preimage_compl] using (hinv q).compl

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.rational_saturation_conull
#print axioms MeasureEquivalenceRestrictedProduct.null_or_conull_of_invariant_and_base_zero_one
