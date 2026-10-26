import ShiftBernoulliMeasure
import PoincareNonreduction
import Definitions.Def_BenchmarkRelations

/-! A precise remaining dependency for the forward finite-ℓp obstruction.
All source-action, median, truncation, summability and null-class arguments
are proved. The theorem below explicitly assumes the Bernoulli scalar
Poincaré bound; proving that bound is still required for an unconditional
benchmark nonreduction. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkShift

def scalarShift (a : Letter) : Point → Point := shift (letterGroup a)

theorem no_lp_reduction_of_scalarPoincare
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hP : BenchmarkPoincareRadial.ScalarPoincareBound p bernoulli scalarShift C) :
    ¬ BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      (BenchmarkComparisons.LpDifference p.toReal) := by
  apply BenchmarkPoincareNonreduction.no_lp_reduction_of_null_classes_and_poincare
    p hp bernoulli Orbit bernoulli_orbit_zero C hC scalarShift
  · intro a
    exact (continuous_shift (letterGroup a)).measurable
  · intro a
    apply ae_of_all
    intro x
    exact (orbit_iff_reachable _ _).mpr (reachable_letter a x).symm
  · exact hP

end BenchmarkShift

#print axioms BenchmarkShift.no_lp_reduction_of_scalarPoincare
