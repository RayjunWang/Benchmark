import RestrictedCompactAction
import SeparatingMultiplierIntertwining
import VectorContinuousState
import MeasureCharacterIntertwining

/-! Actual phase intertwiners force equality of the maximal measure
classes, hence a summable difference of compact parameters. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 800000

namespace MeasureEquivalenceRestrictedPhase

noncomputable section

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureUnitary

local instance : MetricSpace CompactSequences := TopologicalSpace.metrizableSpaceMetric _
local instance : SigmaFinite sampleMeasure := by unfold sampleMeasure; infer_instance

def translatedSampleOrbit (k : CompactSequences) (p : Sample) : CompactSequences :=
  k + sequenceEmbedding (sampleOrbit p)

theorem translatedSampleOrbit_measurable (k : CompactSequences) :
    Measurable (translatedSampleOrbit k) :=
  measurable_const.add (sequenceEmbedding_continuous.measurable.comp sampleOrbit_measurable)

theorem pullbackCharacter_eq_phase (k : CompactSequences) (i : CharacterIndex) (f : CornerHilbert) :
    pullbackMultiplierL2 sampleMeasure (translatedSampleOrbit k) (translatedSampleOrbit_measurable k)
      (characterContinuousMap i) f = phaseUnitary k i f := by
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe sampleMeasure (translatedSampleOrbit k)
    (translatedSampleOrbit_measurable k) (characterContinuousMap i) f,
    phaseUnitary_coe k i f] with p hleft hright
  rw [hleft,hright]
  rfl

theorem continuous_intertwining_of_phase_intertwining (k l : CompactSequences)
    (U : CornerHilbert ≃ₗᵢ[ℂ] CornerHilbert)
    (hU : ∀ i f, U (phaseUnitary k i f) = phaseUnitary l i (U f)) :
    ∀ (c : C(CompactSequences,ℂ)) (f : CornerHilbert),
      U (pullbackMultiplierL2 sampleMeasure (translatedSampleOrbit k)
        (translatedSampleOrbit_measurable k) c f) =
        pullbackMultiplierL2 sampleMeasure (translatedSampleOrbit l)
          (translatedSampleOrbit_measurable l) c (U f) := by
  apply continuous_intertwines_of_separating_family sampleMeasure sampleMeasure
    (translatedSampleOrbit k) (translatedSampleOrbit l)
    (translatedSampleOrbit_measurable k) (translatedSampleOrbit_measurable l)
    characterContinuousMap characterContinuousMap_separates U
  intro i f
  simpa only [pullbackCharacter_eq_phase] using hU i f

def shiftedCompactMeasure (k : CompactSequences) : Measure CompactSequences :=
  compactMeasure.map (fun z => k+z)

theorem shiftedCompactMeasure_sample_class (k : CompactSequences) :
    shiftedCompactMeasure k ≪ sampleMeasure.map (translatedSampleOrbit k) ∧
      sampleMeasure.map (translatedSampleOrbit k) ≪ shiftedCompactMeasure k := by
  have hm : Measurable (fun x : RealSequences => k + sequenceEmbedding x) :=
    measurable_const.add sequenceEmbedding_continuous.measurable
  have heq : shiftedCompactMeasure k =
      restrictedProductMeasure.map (fun x => k + sequenceEmbedding x) := by
    rw [shiftedCompactMeasure,compactMeasure,Measure.map_map (by fun_prop)
      sequenceEmbedding_continuous.measurable]
    rfl
  have hn (B : Set CompactSequences) (hB : MeasurableSet B) :
      sampleMeasure.map (translatedSampleOrbit k) B = 0 ↔ shiftedCompactMeasure k B = 0 := by
    rw [Measure.map_apply (translatedSampleOrbit_measurable k) hB,
      heq,Measure.map_apply hm hB]
    exact translated_spectral_null_iff k B hB
  constructor
  · exact AbsolutelyContinuous.mk (fun B hB hzero => (hn B hB).mp hzero)
  · exact AbsolutelyContinuous.mk (fun B hB hzero => (hn B hB).mpr hzero)

theorem shiftedCompactMeasure_intertwiner_equivalent (k l : CompactSequences)
    (U : CornerHilbert ≃ₗᵢ[ℂ] CornerHilbert)
    (hU : ∀ i f, U (phaseUnitary k i f) = phaseUnitary l i (U f)) :
    shiftedCompactMeasure k ≪ shiftedCompactMeasure l ∧
      shiftedCompactMeasure l ≪ shiftedCompactMeasure k := by
  have h := push_measures_equivalent_of_intertwines_continuous sampleMeasure sampleMeasure
    (translatedSampleOrbit k) (translatedSampleOrbit l)
    (translatedSampleOrbit_measurable k) (translatedSampleOrbit_measurable l) U
    (continuous_intertwining_of_phase_intertwining k l U hU)
  have hk := shiftedCompactMeasure_sample_class k
  have hl := shiftedCompactMeasure_sample_class l
  exact ⟨hk.1.trans (h.1.trans hl.2),hl.1.trans (h.2.trans hk.2)⟩

theorem phase_intertwiner_difference_summable (k l : CompactSequences)
    (U : CornerHilbert ≃ₗᵢ[ℂ] CornerHilbert)
    (hU : ∀ i f, U (phaseUnitary k i f) = phaseUnitary l i (U f)) :
    k-l ∈ summableSubgroup := by
  have h := (shiftedCompactMeasure_intertwiner_equivalent k l U hU).2.map
    (measurable_const.add measurable_id : Measurable (fun z : CompactSequences => -l+z))
  have hleft : (shiftedCompactMeasure l).map (fun z => -l+z) = compactMeasure := by
    rw [shiftedCompactMeasure,Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def,neg_add_cancel_left,Measure.map_id']
  have hright : (shiftedCompactMeasure k).map (fun z => -l+z) =
      compactMeasure.map (fun z => z+(k-l)) := by
    rw [shiftedCompactMeasure,Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    dsimp only [Function.comp_def]
    abel
  rw [hleft,hright] at h
  by_contra hk
  exact compactMeasure_ne_zero (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h
    (compactMeasure_outside_summable_singular (k-l) hk).symm)

end
end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.phase_intertwiner_difference_summable
