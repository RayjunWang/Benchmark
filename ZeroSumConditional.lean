import DenseInvariantAffinity
import CoordinateAffinity

/-! The actual dense rational zero-sum conditional kernel and its
unconditional affinity disintegration for all intrinsic zero-sum shifts. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureEquivalenceRigidity

noncomputable section

open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
  MeasureEquivalenceRNGraph MeasureEquivalenceHellinger
  MeasureEquivalenceErgodicDecomposition MeasureEquivalenceDenseInvariance

def zeroSumGroupHom : Multiplicative zeroSumSpace →* Multiplicative CompactSequences :=
  AddMonoidHom.toMultiplicative zeroSumInclusion

def rationalZeroSumGroup : Subgroup (Multiplicative zeroSumSpace) where
  carrier := {g | g.toAdd ∈ denseRationalSubgroup}
  one_mem' := denseRationalSubgroup.zero_mem
  mul_mem' := denseRationalSubgroup.add_mem
  inv_mem' := denseRationalSubgroup.neg_mem

theorem rationalZeroSumGroup_dense : Dense (rationalZeroSumGroup : Set
    (Multiplicative zeroSumSpace)) := denseRationalSubgroup_dense

instance rationalZeroSumGroup_countable : Countable rationalZeroSumGroup :=
  denseRationalSubgroup_countable.to_subtype

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]

abbrev rationalZeroSumAction : MulAction rationalZeroSumGroup Z :=
  MulAction.compHom Z (zeroSumGroupHom.comp rationalZeroSumGroup.subtype)

noncomputable def zeroSumComponentKernel (M : Measure Z) [IsProbabilityMeasure M] : Kernel Z Z :=
  letI : MulAction rationalZeroSumGroup Z := rationalZeroSumAction
  invariantConditionalKernel (G := rationalZeroSumGroup) M

instance zeroSumComponentKernel_markov (M : Measure Z) [IsProbabilityMeasure M] :
    IsMarkovKernel (zeroSumComponentKernel M) := by
  unfold zeroSumComponentKernel
  infer_instance

variable (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)

include hQI in
theorem zeroSumComponentKernel_affinity (h : zeroSumSpace) :
    affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) =
      ∫ x, affinity (zeroSumComponentKernel M x) ((zeroSumComponentKernel M x).map
        (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) ∂M := by
  letI : PolishSpace (Multiplicative CompactSequences) :=
    inferInstanceAs (PolishSpace CompactSequences)
  letI := upgradeIsCompletelyMetrizable (Multiplicative CompactSequences)
  letI : PolishSpace (Multiplicative zeroSumSpace) :=
    inferInstanceAs (PolishSpace zeroSumSpace)
  letI : MeasurableSpace (Multiplicative zeroSumSpace) := borel (Multiplicative zeroSumSpace)
  letI : BorelSpace (Multiplicative zeroSumSpace) := ⟨rfl⟩
  have hi : Continuous zeroSumGroupHom := zeroSumInclusion_continuous
  have hm (g : Multiplicative zeroSumSpace) :
      zeroSumGroupHom g ∈ quasiInvariantSubgroup M :=
    hQI _ ⟨g.toAdd,g.toAdd.property,rfl⟩
  exact denseInvariant_affinity M zeroSumGroupHom hi hm rationalZeroSumGroup
    rationalZeroSumGroup_dense (Multiplicative.ofAdd h)

include hQI in
theorem zeroSumComponentKernel_coordinate_mean (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ →
      1-ε ≤ ∫ x, affinity (zeroSumComponentKernel M x)
        ((zeroSumComponentKernel M x).map
          (fun z => Multiplicative.ofAdd (coordinateShift a) • z)) ∂M :=
  MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity M
    (zeroSumComponentKernel M) hQI (zeroSumComponentKernel_affinity M hQI) ε hε

end
end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.zeroSumComponentKernel_affinity
#print axioms MeasureEquivalenceRigidity.zeroSumComponentKernel_coordinate_mean
