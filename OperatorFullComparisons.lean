import UnitarySpectralReduction
import OperatorStrictSeparation
import MeasureCyclicReduction

namespace OperatorCoding

/-- Theorem 1.4 of MeasureEquivalence.tex, now Theorem 1.6 of Benchmark.tex. -/
theorem theorem_14_proved : Theorem14 :=
  ⟨⟨cyclicRepresentations_borelReduce_measureEquivalence,
      MeasureUnitary.measureEquivalence_borelReduce_cyclicRepresentations⟩,
    measureEquivalence_borelStrictlyReduce_freeRepresentations,
    freeRepresentations_borelBireducible_boundedOperators⟩

end OperatorCoding

#print axioms OperatorCoding.theorem_14_proved
