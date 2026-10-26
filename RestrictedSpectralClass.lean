import RestrictedPhaseFamily
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid

theorem characterFamily_injective :
    Function.Injective (fun k : CompactSequences => fun i : CharacterIndex => character i k) := by
  intro k l he
  funext n
  apply Subtype.ext
  funext q
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  apply Subtype.ext
  exact congrFun he (n, q)

theorem characterFamily_measurableEmbedding :
    MeasurableEmbedding (fun k : CompactSequences => fun i : CharacterIndex => character i k) :=
  (continuous_pi character_continuous).measurableEmbedding characterFamily_injective

def orbitMeasure : Measure RealSequences := sampleMeasure.map sampleOrbit

theorem orbitMeasure_apply {B : Set RealSequences} (hB : MeasurableSet B) :
    orbitMeasure B = ∑' q : rationalZeroSumGroup, tailProbability ((rationalTranslation q) ⁻¹' B) := by
  rw [orbitMeasure, Measure.map_apply sampleOrbit_measurable hB,
    sampleMeasure, Measure.prod_apply_symm (sampleOrbit_measurable hB), lintegral_count]
  rfl

theorem rationalTranslation_add (q r : rationalZeroSumGroup) (x : RealSequences) :
    rationalTranslation q (rationalTranslation r x) = rationalTranslation (q + r) x := by
  change x + rationalRealShift r + rationalRealShift q = x + rationalRealShift (q + r)
  rw [map_add]
  abel

def saturation (B : Set RealSequences) : Set RealSequences :=
  ⋃ q : rationalZeroSumGroup, (rationalTranslation q) ⁻¹' B

theorem saturation_invariant (B : Set RealSequences) (q : rationalZeroSumGroup) :
    (rationalTranslation q) ⁻¹' saturation B = saturation B := by
  ext x
  simp only [saturation, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r + q, (rationalTranslation_add r q x) ▸ hr⟩
  · rintro ⟨r, hr⟩
    refine ⟨r - q, ?_⟩
    rw [rationalTranslation_add, sub_add_cancel]
    exact hr

theorem orbitMeasure_null_iff {B : Set RealSequences} (hB : MeasurableSet B) :
    orbitMeasure B = 0 ↔ restrictedProductMeasure B = 0 := by
  rw [orbitMeasure_apply hB, ENNReal.tsum_eq_zero]
  constructor
  · intro hzero
    have hs : MeasurableSet (saturation B) := MeasurableSet.iUnion
      (fun q => (measurePreserving_rationalTranslation q).measurable hB)
    have hbase : tailProbability (saturation B) = 0 := by
      exact measure_iUnion_null hzero
    have hz : restrictedProductMeasure (saturation B) = 0 :=
      null_of_invariant_and_base_null (saturation B) hs
        (fun q => Filter.EventuallyEq.of_eq (saturation_invariant B q)) hbase
    apply measure_mono_null _ hz
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    simpa [rationalTranslation] using hx
  · intro hz q
    have ht : restrictedProductMeasure ((rationalTranslation q) ⁻¹' B) = 0 := by
      rw [← Measure.map_apply (measurePreserving_rationalTranslation q).measurable hB,
        (measurePreserving_rationalTranslation q).map_eq, hz]
    have hbase : tailProbability ≪ restrictedProductMeasure := by
      rw [← stageMeasure_zero, ← restrictedProductMeasure_restrict 0]
      exact Measure.restrict_le_self.absolutelyContinuous
    exact hbase ht

theorem translated_spectral_null_iff (k : CompactSequences) (B : Set CompactSequences)
    (hB : MeasurableSet B) :
    sampleMeasure ((fun p : Sample => k + sequenceEmbedding (sampleOrbit p)) ⁻¹' B) = 0 ↔
      restrictedProductMeasure ((fun x : RealSequences => k + sequenceEmbedding x) ⁻¹' B) = 0 := by
  have hpre : MeasurableSet ((fun x : RealSequences => k + sequenceEmbedding x) ⁻¹' B) :=
    (continuous_const.add sequenceEmbedding_continuous).measurable hB
  rw [← orbitMeasure_null_iff hpre, orbitMeasure,
    Measure.map_apply sampleOrbit_measurable hpre]
  rfl

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.characterFamily_measurableEmbedding
#print axioms MeasureEquivalenceRestrictedPhase.orbitMeasure_null_iff
#print axioms MeasureEquivalenceRestrictedPhase.translated_spectral_null_iff
