import CantorProbabilityCoordinates
import MeasureClassClosedCover
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩

/-- The weak-Borel full-support source includes measurably into the exact
canonical Giry measurable space of Cantor probability measures. -/
theorem measurable_fullSupport_probability_inclusion :
    Measurable (fun μ : PositiveCylinderProbabilities => (μ : ProbabilityMeasure HaarCantor)) := by
  have hMeasure : Measurable (fun μ : PositiveCylinderProbabilities =>
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      MeasureUnitary.cantorCylinder_generates.symm MeasureUnitary.cantorCylinder_isPiSystem
    rintro A ⟨k, rfl⟩
    exact ((continuous_clopen_mass_ennreal _ (isClopen_cantorCylinder k)).comp
      continuous_subtype_val).measurable
  exact hMeasure.subtype_mk (h := fun μ => (μ : ProbabilityMeasure HaarCantor).property)

#print axioms measurable_fullSupport_probability_inclusion

end BenchmarkJump
