import BenchmarkResults
import BenchmarkMeasureJumpBridge
import OperatorFullComparisons

/-! The six complete introduction theorems of Benchmark.tex.
All propositions use the exact public mission definitions. -/

namespace BenchmarkComparisons

theorem theorem_1_1 : CountableComparisons := countable_comparisons_proved

theorem theorem_1_2 : ExponentThreshold := exponent_threshold_proved

theorem theorem_1_3 : NullMeasureObstruction := null_measure_obstruction_proved

theorem theorem_1_4 : JumpObstructions := jump_obstructions

theorem theorem_1_5 : OperatorStrictComparison := operator_strict_comparison_proved

theorem theorem_1_6 : RepresentationComparisons := representation_comparisons_proved

theorem all_main_comparisons :
    CountableComparisons ∧ ExponentThreshold ∧ NullMeasureObstruction ∧
      JumpObstructions ∧ OperatorStrictComparison ∧ RepresentationComparisons :=
  ⟨theorem_1_1,theorem_1_2,theorem_1_3,theorem_1_4,theorem_1_5,theorem_1_6⟩

end BenchmarkComparisons

#print axioms BenchmarkComparisons.all_main_comparisons
#print axioms OperatorCoding.theorem_13_proved
#print axioms OperatorCoding.theorem_14_proved
