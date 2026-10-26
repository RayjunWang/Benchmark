import RestrictedInducedTuple

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners

def groupTagEquiv : rationalZeroSumGroup ≃ᵐ RationalGroup where
  toFun := Multiplicative.ofAdd
  invFun := Multiplicative.toAdd
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem groupTag_preserving : MeasurePreserving groupTagEquiv
    (Measure.count : Measure rationalZeroSumGroup) (Measure.count : Measure RationalGroup) := by
  refine ⟨groupTagEquiv.measurable, ?_⟩
  ext S hS
  rw [Measure.map_apply groupTagEquiv.measurable hS]
  have he : groupTagEquiv ⁻¹' S = groupTagEquiv.symm '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨groupTagEquiv x, hx, groupTagEquiv.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, MeasurableEquiv.apply_symm_apply] using hy
  rw [he]
  exact Measure.count_injective_image groupTagEquiv.symm.injective S

def sampleTagEquiv : Sample ≃ᵐ (RealSequences × RationalGroup) :=
  (MeasurableEquiv.refl RealSequences).prodCongr groupTagEquiv

theorem sampleTag_preserving : MeasurePreserving sampleTagEquiv sampleMeasure
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  rw [base_corner_measure_eq_base_product]
  exact (MeasurePreserving.id tailProbability).prod groupTag_preserving

def inducedObservable (k : CompactSequences) (p : RealSequences × RationalGroup) : CompactSequences :=
  k + sequenceEmbedding (orbitPoint p)

theorem inducedObservable_measurable (k : CompactSequences) : Measurable (inducedObservable k) :=
  measurable_const.add (sequenceEmbedding_continuous.measurable.comp orbitPoint_measurable)

theorem inducedObservable_tag (k : CompactSequences) (p : Sample) :
    inducedObservable k (sampleTagEquiv p) = k + sequenceEmbedding (sampleOrbit p) := rfl

theorem induced_spectral_null_iff (k : CompactSequences) (B : Set CompactSequences)
    (hB : MeasurableSet B) :
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
        ((inducedObservable k) ⁻¹' B) = 0 ↔
      restrictedProductMeasure ((fun x : RealSequences => k + sequenceEmbedding x) ⁻¹' B) = 0 := by
  rw [← sampleTag_preserving.measure_preimage
    ((inducedObservable_measurable k) hB).nullMeasurableSet]
  exact translated_spectral_null_iff k B hB

theorem induced_push_spectral_null_iff (k : CompactSequences) (B : Set CompactSequences)
    (hB : MeasurableSet B) :
    ((cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)).map
      (inducedObservable k)) B = 0 ↔
      (compactMeasure.map (fun z => z + k)) B = 0 := by
  rw [Measure.map_apply (inducedObservable_measurable k) hB, induced_spectral_null_iff k B hB,
    compactMeasure, Measure.map_map (by fun_prop) sequenceEmbedding_continuous.measurable,
    Measure.map_apply ((by fun_prop : Measurable (fun z : CompactSequences => z + k)).comp
      sequenceEmbedding_continuous.measurable) hB]
  have he : (fun x : RealSequences => k + sequenceEmbedding x) =
      ((fun z : CompactSequences => z + k) ∘ sequenceEmbedding) := by
    funext x
    exact add_comm _ _
  rw [he]

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.induced_spectral_null_iff
#print axioms MeasureEquivalenceRestrictedPhase.induced_push_spectral_null_iff
