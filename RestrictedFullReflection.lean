import RestrictedFiniteCornerReflection
import ScalarMeasureNormalization

/-! Exact reflection of the zero-sum subgroup by the actual induced
unitary tuple. The normalization, trace comparison and summability
reflection are all constructed in the imported checked developments. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1500000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

local instance : SigmaFinite (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  unfold cornerMeasure
  infer_instance

def normalizedTranslation (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    InducedHilbert ≃ₗᵢ[ℂ] TranslatedHilbert h :=
  (scalarMeasureEquiv (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
    (translationScale h) (translationScale_ne_zero h)).symm.trans (translatedCornerPullback h hs)

theorem normalizedTranslation_coe (h : RealSequences) (hs : Summable (fun n => |h n|))
    (u : InducedHilbert) :
    normalizedTranslation h hs u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
      fun p => (Real.sqrt (translationScale h : ℝ))⁻¹ • u (translatedCornerEquiv h p) := by
  filter_upwards [translatedCornerPullback_coe h hs
      ((scalarMeasureEquiv (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
        (translationScale h) (translationScale_ne_zero h)).symm u),
    (translatedCorner_preserving h hs).quasiMeasurePreserving.ae
      (scalarMeasureEquiv_symm_coe
        (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
          (translationScale h) (translationScale_ne_zero h) u)] with p hp hscl
  exact hp.trans hscl

theorem inducedTuple_intertwiner_difference_zeroSum (k l : CompactSequences)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) :
    k - l ∈ zeroSumSubgroup := by
  have hsum := inducedTuple_intertwiner_difference_summable k l W hW
  have hlk : l - k ∈ summableSubgroup := by
    simpa only [neg_sub] using summableSubgroup.neg_mem hsum
  obtain ⟨h, he⟩ := hlk
  have hs : Summable (fun n => |h n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.memℓp h).summable (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)
  have he' : k + sequenceEmbedding (h : RealSequences) = l := by
    change k + l1Embedding h = l
    rw [he]
    abel
  have hzero := total_eq_zero_of_normalized_intertwiner (h : RealSequences) hs k l he' W hW
    (normalizedTranslation (h : RealSequences) hs) (Real.sqrt (translationScale (h : RealSequences) : ℝ))⁻¹
    (normalizedTranslation_coe (h : RealSequences) hs)
  have hH : l - k ∈ zeroSumSubgroup := by
    rw [← he]
    exact (l1Embedding_mem_zeroSumSubgroup h).mpr hzero
  simpa only [neg_sub] using zeroSumSubgroup.neg_mem hH

theorem inducedTuple_intertwiner_iff_zeroSum (k l : CompactSequences) :
    (∃ W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert,
      ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) ↔
        k - l ∈ zeroSumSubgroup := by
  constructor
  · rintro ⟨W, hW⟩
    exact inducedTuple_intertwiner_difference_zeroSum k l W hW
  · intro hkl
    apply exists_inducedTuple_intertwiner_of_zeroSum k l
    simpa only [neg_sub] using zeroSumSubgroup.neg_mem hkl

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.inducedTuple_intertwiner_iff_zeroSum
