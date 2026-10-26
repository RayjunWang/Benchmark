import BernoulliMedianGap
import PoincareNonreduction
import Definitions.Def_BenchmarkRelations

/-! The unconditional finite-ℓp obstruction for the actual full free-group shift.
The scalar Poincaré inequality, atomlessness, and nullity of every orbit are
proved in the imported modules; this theorem has no classification hypothesis. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkShift

theorem eInfinity_not_reduces_ENNlp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ¬ BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      (BenchmarkComparisons.LpDifference p.toReal) := by
  apply BenchmarkPoincareNonreduction.no_lp_reduction_of_null_classes_and_poincare
    p hp bernoulli Orbit bernoulli_orbit_zero
    (ENNReal.ofReal (2 * powerGapConstant p.toReal)) ENNReal.ofReal_ne_top inverseGeneratorShift
  · intro i
    exact (continuous_shift (letterGroup (i, true))⁻¹).measurable
  · intro i
    apply ae_of_all
    intro x
    exact (orbit_iff_reachable _ _).mpr
      (reachable_shift (letterGroup (i, true))⁻¹ x).symm
  · exact scalarPoincare_inverseGenerators p hp

theorem eInfinity_not_reduces_finiteLp (p : ℝ) (hp : 1 ≤ p) :
    ¬ BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      (BenchmarkComparisons.LpDifference p) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have h := eInfinity_not_reduces_ENNlp (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (le_trans zero_le_one hp)] using h

end BenchmarkShift

#print axioms BenchmarkShift.eInfinity_not_reduces_finiteLp
