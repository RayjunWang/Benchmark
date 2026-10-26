import ZeroSumAffinity
import HellingerOrbit

/-! The actual compact-limit step in the quasi-invariance rigidity proof.
Upper semicontinuity of the averaged affinity transports uniform intrinsic
zero-sum estimates to a one-coordinate shift. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Topology ENNReal

namespace MeasureEquivalenceZeroSumAffinity

open MeasureEquivalenceSolenoid MeasureEquivalenceHellinger
  MeasureEquivalenceRNGraph MeasureEquivalenceRootContinuity

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (κ : Kernel Z Z) [IsMarkovKernel κ]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)
    (hsplit : ∀ h : zeroSumSpace,
      affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) =
        ∫ x, affinity (κ x) ((κ x).map
          (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) ∂M)

include hQI hsplit in
theorem uniform_coordinate_mean_affinity (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ →
      1 - ε ≤ ∫ x, affinity (κ x) ((κ x).map
        (fun z => Multiplicative.ofAdd (coordinateShift a) • z)) ∂M := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure M
  letI : PolishSpace (Multiplicative CompactSequences) :=
    inferInstanceAs (PolishSpace CompactSequences)
  letI := upgradeIsCompletelyMetrizable (Multiplicative CompactSequences)
  obtain ⟨δ,hδ,hbound⟩ := uniform_twoPoint_affinity M hQI ε hε
  refine ⟨δ,hδ,?_⟩
  intro a ha
  let F : Multiplicative CompactSequences → ℝ := fun g =>
    ∫ x, affinity (κ x) ((κ x).map (fun z => g • z)) ∂M
  have hu : UpperSemicontinuous F :=
    upperSemicontinuous_integrated_affinity_standardBorel M κ
  have hclosed : IsClosed {g | 1-ε ≤ F g} := hu.isClosed_preimage (1-ε)
  have ht : Tendsto (fun n => Multiplicative.ofAdd (l1Embedding (twoPoint a n)))
      atTop (𝓝 (Multiplicative.ofAdd (coordinateShift a))) := twoPoint_limit a
  apply hclosed.mem_of_tendsto ht
  apply Eventually.of_forall
  intro n
  change 1-ε ≤ F (Multiplicative.ofAdd (l1Embedding (twoPoint a n)))
  have hs := hsplit ⟨twoPoint a n,twoPoint_zeroSum a n⟩
  change affinity M (M.map (fun z => Multiplicative.ofAdd
    (l1Embedding (twoPoint a n)) • z)) = F (Multiplicative.ofAdd
      (l1Embedding (twoPoint a n))) at hs
  rw [← hs]
  exact hbound a ha n

end MeasureEquivalenceZeroSumAffinity

#print axioms MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity
