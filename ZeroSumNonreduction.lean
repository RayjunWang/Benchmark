import CompactAveraging
import SolenoidGroups
import RNGraph
import ZeroSumRigidity

/-! Compact Haar averaging turns a hypothetical reduction of the actual
zero-sum coset relation into a probability whose exact quasi-invariance
subgroup is that zero-sum subgroup. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceCompactAveraging MeasureEquivalenceResearch
  MeasureEquivalenceSolenoid MeasureEquivalenceRNGraph

abbrev CantorSample := ℕ → Bool

section Averaging

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated CompactSequences Y]

/-- The probability is constructed from normalized Haar measure and
the actual Markov kernel supplied by the proposed measurable reduction. -/
theorem zeroSum_probability_reduction_averaging
    (f : CompactSequences → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔
      x - y ∈ zeroSumSubgroup) :
    letI := baseTranslationAction CompactSequences Y
    letI : ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × Y) :=
      continuous_baseTranslationAction CompactSequences Y
    ∃ M : Measure (CompactSequences × Y), IsProbabilityMeasure M ∧
      ∀ g : Multiplicative CompactSequences,
        g ∈ quasiInvariantSubgroup M ↔ g.toAdd ∈ zeroSumSubgroup := by
  letI := baseTranslationAction CompactSequences Y
  letI : ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × Y) :=
    continuous_baseTranslationAction CompactSequences Y
  refine ⟨averagedMeasure (compactHaar CompactSequences) f hf, inferInstance, ?_⟩
  intro g
  rw [mem_quasiInvariantSubgroup_iff]
  exact exact_quasi_invariance_action zeroSumSubgroup f hf hred g

end Averaging

/-- All topological and measure-theoretic structures required by
rigidity hold on the concrete compact product used for Cantor measures. -/
theorem cantor_product_translation_continuous :
    letI := baseTranslationAction CompactSequences CantorSample
    ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × CantorSample) :=
  continuous_baseTranslationAction CompactSequences CantorSample

example : CompactSpace (CompactSequences × CantorSample) := inferInstance
example : MetrizableSpace (CompactSequences × CantorSample) := inferInstance
example : BorelSpace (CompactSequences × CantorSample) := inferInstance

/-- The actual compact zero-sum coset relation does not admit a
measurable reduction to mutual absolute continuity of Cantor probabilities.
No rigidity, disintegration, or conditional ergodicity premise is assumed. -/
theorem zeroSum_not_reducible_to_measure_equivalence :
    ¬ ∃ f : CompactSequences → ProbabilityMeasure CantorSample,
      Measurable f ∧ ∀ x y,
        EquivalentMeasures (f x : Measure CantorSample) (f y : Measure CantorSample) ↔
          x - y ∈ zeroSumSubgroup := by
  rintro ⟨f, hf, hred⟩
  letI : MetricSpace (CompactSequences × CantorSample) :=
    TopologicalSpace.metrizableSpaceMetric (CompactSequences × CantorSample)
  letI := baseTranslationAction CompactSequences CantorSample
  letI : ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × CantorSample) :=
    continuous_baseTranslationAction CompactSequences CantorSample
  obtain ⟨M, hM, hexact⟩ := zeroSum_probability_reduction_averaging f hf hred
  letI : IsProbabilityMeasure M := hM
  have hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M :=
    fun h hh => (hexact (Multiplicative.ofAdd h)).mpr hh
  have h1 := coordinateShift_quasiInvariant M hQI 1
  have hH := (hexact (Multiplicative.ofAdd (coordinateShift 1))).mp h1
  have hz : (1 : ℝ) = 0 := (coordinateShift_mem_zeroSum 1).mp hH
  norm_num at hz

end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.zeroSum_probability_reduction_averaging
#print axioms MeasureEquivalenceRigidity.cantor_product_translation_continuous
#print axioms MeasureEquivalenceRigidity.zeroSum_not_reducible_to_measure_equivalence
