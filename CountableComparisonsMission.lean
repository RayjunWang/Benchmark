import CountablePositiveMission
import ShiftFiniteLpObstruction
import LpCountableObstruction

/-! The exact complete benchmark mission statement for Theorem 1.1. -/

namespace BenchmarkCountableComparisons

theorem countable_comparisons : BenchmarkComparisons.CountableComparisons := by
  refine ⟨BenchmarkCountablePositive.product_eInfinity_reduces_null, ?_⟩
  intro p hp
  exact ⟨BenchmarkShift.eInfinity_not_reduces_finiteLp p hp,
    BenchmarkCountableReverse.finiteLp_not_reduces_eInfinity p hp⟩

end BenchmarkCountableComparisons

#print axioms BenchmarkCountableComparisons.countable_comparisons
