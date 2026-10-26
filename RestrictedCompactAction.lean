import RestrictedCompactMeasure

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid

theorem compactMeasure_base : compactMeasure (sequenceEmbedding '' stageSet 0) = 1 := by
  rw [compactMeasure, sequenceEmbedding_measurableEmbedding.map_apply,
    sequenceEmbedding_injective.preimage_image, restrictedProductMeasure_base]

theorem compactMeasure_univ : compactMeasure univ = ∞ := by
  rw [compactMeasure, Measure.map_apply sequenceEmbedding_continuous.measurable MeasurableSet.univ,
    preimage_univ, restrictedProductMeasure_univ]

theorem compactMeasure_ne_zero : compactMeasure ≠ 0 := by
  intro he
  have hh := compactMeasure_base
  simp [he] at hh

def compactTranslation (q : rationalZeroSumGroup) (k : CompactSequences) : CompactSequences :=
  k + sequenceEmbedding (rationalRealShift q)

theorem compactTranslation_measurable (q : rationalZeroSumGroup) : Measurable (compactTranslation q) :=
  measurable_id.add_const _

theorem compactTranslation_preserving (q : rationalZeroSumGroup) :
    MeasurePreserving (compactTranslation q) compactMeasure compactMeasure := by
  refine ⟨compactTranslation_measurable q, ?_⟩
  change compactMeasure.map (fun z => z + sequenceEmbedding (rationalRealShift q)) = compactMeasure
  rw [compactMeasure_translate_real]
  change (restrictedProductMeasure.map (rationalTranslation q)).map sequenceEmbedding = compactMeasure
  rw [(measurePreserving_rationalTranslation q).map_eq]
  rfl

theorem compactTranslation_free (q : rationalZeroSumGroup) (k : CompactSequences) :
    compactTranslation q k = k ↔ q = 0 := by
  constructor
  · intro he
    have hz : sequenceEmbedding (rationalRealShift q) = 0 :=
      add_left_cancel (show k + sequenceEmbedding (rationalRealShift q) = k + 0 from by
        simpa only [compactTranslation, add_zero] using he)
    have hr : rationalRealShift (q : ℕ →₀ ℚ) = 0 := by
      apply sequenceEmbedding_injective
      simpa only [map_zero] using hz
    apply Subtype.ext
    apply rationalRealShift_injective
    simpa using hr
  · rintro rfl
    simp [compactTranslation]

theorem compactTranslation_ergodic (E : Set CompactSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (compactTranslation q) ⁻¹' E =ᵐ[compactMeasure] E) :
    compactMeasure E = 0 ∨ compactMeasure Eᶜ = 0 := by
  have hm : MeasurePreserving sequenceEmbedding restrictedProductMeasure compactMeasure :=
    ⟨sequenceEmbedding_continuous.measurable, rfl⟩
  have hi (q : rationalZeroSumGroup) :
      (rationalTranslation q) ⁻¹' (sequenceEmbedding ⁻¹' E)
        =ᵐ[restrictedProductMeasure] sequenceEmbedding ⁻¹' E := by
    have hh := hm.quasiMeasurePreserving.ae_eq (hinv q)
    filter_upwards [hh] with x hx
    change E (sequenceEmbedding x + sequenceEmbedding (rationalRealShift q)) = E (sequenceEmbedding x) at hx
    change E (sequenceEmbedding (x + rationalRealShift q)) = E (sequenceEmbedding x)
    rw [map_add]
    exact hx
  have hz := rationalZeroSum_ergodic (sequenceEmbedding ⁻¹' E)
    (sequenceEmbedding_continuous.measurable hE) hi
  simpa only [compactMeasure, Measure.map_apply sequenceEmbedding_continuous.measurable hE,
    Measure.map_apply sequenceEmbedding_continuous.measurable hE.compl, preimage_compl] using hz

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.compactTranslation_preserving
#print axioms MeasureEquivalenceRestrictedPhase.compactTranslation_ergodic
