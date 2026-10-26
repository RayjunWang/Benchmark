import MeasureLocalSmallRows
import MeasureInterpolationChain
import MeasureCategory
import CantorProbabilityMixOpen
import WeakGiryInclusion

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩

/-- The unconditional local output-row property for actual measure equivalence.
All bundle, Hellinger, interpolation, and category inputs have been proved. -/
theorem measure_local_rows
    (F : PositiveCylinderProbabilities → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism FullSupportMeasureEquivalence (Jump BoundedDifference) F) :
    LocallyGenericallyConstantRows BoundedDifference F := by
  intro k A hAo hAn
  obtain ⟨O, D, ε, n, hOo, hOn, hOA, hOconvex, hε, hD, _hf, hSmall⟩ :=
    measure_local_small_rows F hFm hF k A hAo hAn
  obtain ⟨a, ha⟩ := measure_interpolation_constant_on_open isOpenMap_positiveProbabilityMix
    O hOo hOn hOconvex D hD (fun μ => F μ k) ε hε
    (fun μ hμ ν hν hμD hνD hE => ⟨n, hSmall μ hμ ν hν hμD hνD hE⟩)
  exact ⟨O, a, hOo, hOn, hOA, ha⟩

/-- Actual full-support Cantor measure equivalence has no Borel reduction
to the Friedman--Stanley jump of bounded difference. -/
theorem fullSupport_measure_not_borel_reducible_to_jump :
    ¬ ∃ F : PositiveCylinderProbabilities → ℕ → RealSequences, Measurable F ∧
      ∀ μ ν, FullSupportMeasureEquivalence μ ν ↔ Jump BoundedDifference (F μ) (F ν) :=
  not_borel_reduction_of_local_rows FullSupportMeasureEquivalence BoundedDifference
    boundedDifference_equivalence measurableSet_boundedDifference
    fullSupportMeasureEquivalence_genericallyErgodic fullSupportMeasureEquivalence_class_meagre
    measure_local_rows

/-- The measure-equivalence half of Theorem1.4 on the complete actual space
of Cantor probability measures. -/
theorem measure_not_borel_reducible_to_boundedDifferenceJump :
    ¬ ∃ F : ProbabilityMeasure HaarCantor → ℕ → RealSequences, Measurable F ∧
      ∀ μ ν : ProbabilityMeasure HaarCantor,
        (((μ : Measure HaarCantor) ≪ (ν : Measure HaarCantor)) ∧
          ((ν : Measure HaarCantor) ≪ (μ : Measure HaarCantor))) ↔
        Jump BoundedDifference (F μ) (F ν) := by
  rintro ⟨F, hFm, hRed⟩
  apply fullSupport_measure_not_borel_reducible_to_jump
  refine ⟨F ∘ Subtype.val, hFm.comp measurable_fullSupport_probability_inclusion, ?_⟩
  intro μ ν
  exact hRed μ ν

#print axioms measure_local_rows
#print axioms fullSupport_measure_not_borel_reducible_to_jump
#print axioms measure_not_borel_reducible_to_boundedDifferenceJump

end BenchmarkJump
