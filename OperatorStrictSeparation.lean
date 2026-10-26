import RestrictedFullReflection
import MeasureInducedOperatorEquivalence
import ZeroSumNonreduction
import MeasureOperatorReduction

/-! Unconditional strict separation of measure equivalence from unitary
equivalence of all bounded operators, via the concrete compact zero-sum
quotient and the actual continuous bounded-operator family. -/

open MeasureTheory OperatorCoding

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceSolenoid

theorem inducedCodedOperator_equivalent_iff_zeroSum (k l : CompactSequences) :
    OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l) ↔
      k - l ∈ zeroSumSubgroup :=
  (inducedCodedOperator_equivalent_iff k l).trans (inducedTuple_intertwiner_iff_zeroSum k l)

theorem zeroSum_borelReduce_boundedOperators :
    BorelReducesWith (inferInstance : MeasurableSpace CompactSequences) operatorBorel
      (fun k l => k - l ∈ zeroSumSubgroup) OperatorUnitaryEquivalent :=
  ⟨inducedCodedOperator, inducedCodedOperator_measurable,
    fun k l => (inducedCodedOperator_equivalent_iff_zeroSum k l).symm⟩

end MeasureEquivalenceRestrictedPhase

namespace OperatorCoding

open MeasureUnitary MeasureEquivalenceRestrictedPhase MeasureEquivalenceSolenoid
  MeasureEquivalenceRigidity MeasureEquivalenceResearch

theorem boundedOperators_not_borelReduce_measureEquivalence :
    ¬ BorelReducesWith operatorBorel (inferInstance : MeasurableSpace (ProbabilityMeasure Cantor))
      OperatorUnitaryEquivalent MeasureEquivalent := by
  rintro ⟨f, hf, hred⟩
  apply zeroSum_not_reducible_to_measure_equivalence
  refine ⟨f ∘ inducedCodedOperator, hf.comp inducedCodedOperator_measurable, ?_⟩
  intro k l
  exact (hred (inducedCodedOperator k) (inducedCodedOperator l)).symm.trans
    (inducedCodedOperator_equivalent_iff_zeroSum k l)

/-- Theorem 1.3 of MeasureEquivalence.tex, now Theorem 1.5 of Benchmark.tex. -/
theorem theorem_13_proved : Theorem13 :=
  ⟨measureEquivalence_borelReduce_boundedOperators,
    boundedOperators_not_borelReduce_measureEquivalence⟩

theorem freeRepresentations_not_borelReduce_measureEquivalence :
    ¬ BorelReducesWith (unitaryRepresentationBorel (FreeGroup ℕ))
      (inferInstance : MeasurableSpace (ProbabilityMeasure Cantor))
      UnitaryRepresentationEquivalent MeasureEquivalent := by
  intro h
  exact boundedOperators_not_borelReduce_measureEquivalence
    (borelReducesWith_trans boundedOperators_borelReduce_freeRepresentations h)

theorem measureEquivalence_borelStrictlyReduce_freeRepresentations :
    BorelStrictlyReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure Cantor))
      (unitaryRepresentationBorel (FreeGroup ℕ)) MeasureEquivalent UnitaryRepresentationEquivalent :=
  ⟨borelReducesWith_trans measureEquivalence_borelReduce_boundedOperators
    boundedOperators_borelReduce_freeRepresentations,
    freeRepresentations_not_borelReduce_measureEquivalence⟩

end OperatorCoding

#print axioms OperatorCoding.theorem_13_proved
#print axioms OperatorCoding.measureEquivalence_borelStrictlyReduce_freeRepresentations
