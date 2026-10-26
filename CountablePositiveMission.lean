import ShiftNullReduction
import Definitions.Def_BenchmarkRelations

/-! Exact Prove2Me mission interfaces for the positive part of Theorem 1.1.
The nonreductions against finite ℓp are separate statements. -/

namespace BenchmarkCountablePositive

theorem eInfinity_reduces_null :
    BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      BenchmarkComparisons.NullDifference := by
  obtain ⟨F, hF, _hb, hr⟩ := BenchmarkShift.exists_borel_shift_null_reduction
  exact ⟨F, hF, hr⟩

theorem product_eInfinity_reduces_null :
    BenchmarkComparisons.BorelReduces
      (BenchmarkComparisons.ProductRelation BenchmarkComparisons.EInfinity)
      BenchmarkComparisons.NullDifference := by
  obtain ⟨F, hF, _hb, hr⟩ := BenchmarkShift.exists_borel_product_shift_null_reduction
  exact ⟨F, hF, hr⟩

end BenchmarkCountablePositive

#print axioms BenchmarkCountablePositive.eInfinity_reduces_null
#print axioms BenchmarkCountablePositive.product_eInfinity_reduces_null
