import DensityInversion
import WeightedRootSwitch

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem root_densityTarget_eq (z : PositiveDensityBundle) :
    MeasureEquivalenceHellinger.root
      ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) = densityVector z := by
  have hPos : 0 ≤ densityVector z :=
    (Lp.coeFn_nonneg _).mp ((densityVector_positive z).mono fun _ hx => hx.le)
  apply MeasureEquivalenceDensity.squareMeasure_injective_nonnegative
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (MeasureEquivalenceHellinger.root_nonnegative _ _) hPos
  apply Subtype.ext
  exact MeasureEquivalenceRNGraph.squareMeasure_root
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (by exact densityTarget_ac_source z)

/-- Actual inversion formula for every real test function; no continuity or
integrability of the test is required for this identity. -/
theorem integral_inverseDensityVector (z : PositiveDensityBundle) (g : HaarCantor → ℝ) :
    (∫ x, g x * inverseDensityVector z x
      ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) =
      ∫ x, g x * densityVector z x
        ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  have hSwitch := weighted_root_switch g
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (densitySource_ac_target z) (densityTarget_ac_source z)
  rw [root_densityTarget_eq] at hSwitch
  exact hSwitch

#print axioms integral_inverseDensityVector

end BenchmarkJump
