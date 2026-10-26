import RestrictedInducedSpectral
import VectorContinuousState
import MeasureCharacterIntertwining

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 800000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureUnitary
open MeasureEquivalenceInducedCorners

local instance : MetricSpace CompactSequences := TopologicalSpace.metrizableSpaceMetric _

abbrev inducedSampleMeasure :=
  cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)

local instance : SigmaFinite inducedSampleMeasure := by
  change SigmaFinite (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
  rw [base_corner_measure_eq_base_product]
  infer_instance

theorem pullbackCharacter_eq_inducedPhase (k : CompactSequences) (i : CharacterIndex)
    (f : InducedHilbert) :
    pullbackMultiplierL2 inducedSampleMeasure (inducedObservable k) (inducedObservable_measurable k)
      (characterContinuousMap i) f = inducedFamilyPhase k i f := by
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe inducedSampleMeasure (inducedObservable k)
    (inducedObservable_measurable k) (characterContinuousMap i) f,
    inducedFamilyPhase_coe k i f] with p hleft hright
  rw [hleft, hright]
  rfl

theorem continuous_intertwining_of_inducedPhase_intertwining (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ i f, U (inducedFamilyPhase k i f) = inducedFamilyPhase l i (U f)) :
    ∀ (c : C(CompactSequences, ℂ)) (f : InducedHilbert),
      U (pullbackMultiplierL2 inducedSampleMeasure (inducedObservable k)
        (inducedObservable_measurable k) c f) =
        pullbackMultiplierL2 inducedSampleMeasure (inducedObservable l)
          (inducedObservable_measurable l) c (U f) := by
  apply continuous_intertwines_of_separating_family inducedSampleMeasure inducedSampleMeasure
    (inducedObservable k) (inducedObservable l)
    (inducedObservable_measurable k) (inducedObservable_measurable l)
    characterContinuousMap characterContinuousMap_separates U
  intro i f
  simpa only [pullbackCharacter_eq_inducedPhase] using hU i f

def inducedCompactShift (k : CompactSequences) : Measure CompactSequences :=
  compactMeasure.map (fun z => z + k)

theorem inducedCompactShift_sample_class (k : CompactSequences) :
    inducedCompactShift k ≪ inducedSampleMeasure.map (inducedObservable k) ∧
      inducedSampleMeasure.map (inducedObservable k) ≪ inducedCompactShift k := by
  constructor
  · exact AbsolutelyContinuous.mk (fun B hB hz => (induced_push_spectral_null_iff k B hB).mp hz)
  · exact AbsolutelyContinuous.mk (fun B hB hz => (induced_push_spectral_null_iff k B hB).mpr hz)

theorem inducedCompactShift_intertwiner_equivalent (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ i f, U (inducedFamilyPhase k i f) = inducedFamilyPhase l i (U f)) :
    inducedCompactShift k ≪ inducedCompactShift l ∧ inducedCompactShift l ≪ inducedCompactShift k := by
  have h := push_measures_equivalent_of_intertwines_continuous inducedSampleMeasure inducedSampleMeasure
    (inducedObservable k) (inducedObservable l)
    (inducedObservable_measurable k) (inducedObservable_measurable l) U
    (continuous_intertwining_of_inducedPhase_intertwining k l U hU)
  have hk := inducedCompactShift_sample_class k
  have hl := inducedCompactShift_sample_class l
  exact ⟨hk.1.trans (h.1.trans hl.2), hl.1.trans (h.2.trans hk.2)⟩

theorem inducedPhase_intertwiner_difference_summable (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ i f, U (inducedFamilyPhase k i f) = inducedFamilyPhase l i (U f)) :
    k - l ∈ summableSubgroup := by
  have h := (inducedCompactShift_intertwiner_equivalent k l U hU).2.map
    (by fun_prop : Measurable (fun z : CompactSequences => z - l))
  have hleft : (inducedCompactShift l).map (fun z => z - l) = compactMeasure := by
    rw [inducedCompactShift, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, add_sub_cancel_right, Measure.map_id']
  have hright : (inducedCompactShift k).map (fun z => z - l) =
      compactMeasure.map (fun z => z + (k - l)) := by
    rw [inducedCompactShift, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    dsimp only [Function.comp_def]
    abel
  rw [hleft, hright] at h
  by_contra hk
  exact compactMeasure_ne_zero (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h
    (compactMeasure_outside_summable_singular (k - l) hk).symm)

theorem inducedTuple_intertwiner_difference_summable (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ n f, U (inducedTuple k n f) = inducedTuple l n (U f)) :
    k - l ∈ summableSubgroup :=
  inducedPhase_intertwiner_difference_summable k l U
    (intertwines_generators_of_intertwines_tuple k l U hU).1

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.inducedPhase_intertwiner_difference_summable
#print axioms MeasureEquivalenceRestrictedPhase.inducedTuple_intertwiner_difference_summable
