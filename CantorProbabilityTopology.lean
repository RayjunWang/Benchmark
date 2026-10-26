import CantorHaarCylinders
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Polish
import GdeltaPolish

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- The actual weak topology on Cantor probability measures is Polish.
Compactness is Prokhorov's theorem; metrizability is the actual weak
Lévy--Prokhorov topology, with no replacement measurable structure. -/
theorem cantorProbability_polish : PolishSpace (ProbabilityMeasure HaarCantor) := by
  letI : MetricSpace (ProbabilityMeasure HaarCantor) :=
    TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure HaarCantor)
  infer_instance

/-- Positivity on every genuine finite binary-prefix cylinder defines a
Polish subspace with its inherited weak topology. -/
theorem positiveCylinderProbabilities_polish : PolishSpace PositiveCylinderProbabilities := by
  letI : PolishSpace (ProbabilityMeasure HaarCantor) := cantorProbability_polish
  exact polishSpace_of_isGdelta isGδ_positiveCylinderProbabilities

#print axioms cantorProbability_polish
#print axioms positiveCylinderProbabilities_polish

end BenchmarkJump
