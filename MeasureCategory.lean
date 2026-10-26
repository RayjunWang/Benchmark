import CantorReweightOrbitDensity
import MeasureClassMeagre
import CantorFullSupportWitness

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem fullSupportMeasureEquivalence_genericallyErgodic :
    GenericallyErgodic FullSupportMeasureEquivalence :=
  fullSupportMeasureEquivalence_genericallyErgodic_of_dense_reweights
    continuousSquareReweight_orbit_dense

theorem fullSupportMeasureEquivalence_class_meagre (μ : PositiveCylinderProbabilities) :
    IsMeagre {ν | FullSupportMeasureEquivalence ν μ} := by
  apply (measure_equivalence_class_meagre μ).mono
  intro ν hν
  exact ⟨hν.2, hν.1⟩

#print axioms fullSupportMeasureEquivalence_genericallyErgodic
#print axioms fullSupportMeasureEquivalence_class_meagre

end BenchmarkJump
