import Definitions.Def_BenchmarkRelations
import SequenceTheorems
import OperatorStrictSeparation
import CountableComparisonsMission
import BenchmarkOperatorTransport
import BenchmarkJumpBridge

namespace BenchmarkComparisons

/-- Theorem 1.1, including both nonreductions for every finite exponent. -/
theorem countable_comparisons_proved : CountableComparisons :=
  BenchmarkCountableComparisons.countable_comparisons

/-- Theorem 1.2 of Benchmark.tex, including the infinite exponent. -/
theorem exponent_threshold_proved : ExponentThreshold := by
  intro p hp
  exact MeasureEquivalencePaper.theorem_1_1 p hp

/-- Theorem 1.3 of Benchmark.tex. -/
theorem null_measure_obstruction_proved : NullMeasureObstruction := by
  exact MeasureEquivalencePaper.theorem_1_2

/-- Theorem 1.5 of Benchmark.tex (Theorem 1.3 of the earlier manuscript). -/
theorem operator_strict_comparison_proved : OperatorStrictComparison := by
  exact OperatorCoding.theorem_13_proved

end BenchmarkComparisons

#print axioms BenchmarkComparisons.exponent_threshold_proved
#print axioms BenchmarkComparisons.null_measure_obstruction_proved
#print axioms BenchmarkComparisons.operator_strict_comparison_proved
#print axioms BenchmarkComparisons.countable_comparisons_proved
#print axioms BenchmarkComparisons.representation_comparisons_proved
