import RNPresentation
import SolenoidGroups

/-! Actual Radon--Nikodym root continuity for the zero-sum l1 subgroup.
The general closed-graph argument is reused from the archived sequence-space
development. No continuity of densities is assumed. -/

open MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceRootContinuity

open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph

section General

variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem continuous_root_of_mem (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M) :
    Continuous (fun g => root (orbit M (i g) : Measure Z) M) := by
  letI : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let Q := GraphGroup (quasiInvariantSubgroup (K := A) M) (feature M)
  letI : IsTopologicalGroup Q := graphGroup_topologicalGroup _ _ (feature_mul_left M)
  letI : PolishSpace Q := graphGroup_polish _ _ (isClosed_graph M)
  letI : SecondCountableTopology Q := inferInstance
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  let j : G →* Q := i.codRestrict _ hmem
  have hj : Measurable j := by
    apply ((inclusion_continuous _ _).measurableEmbedding
      (inclusion_injective _ _)).measurable_comp_iff.mp
    exact hi.measurable
  have hc : Continuous j := MeasureEquivalenceTopology.continuous_borel_hom j hj
  exact continuous_subtype_val.comp ((feature_continuous _ _).comp hc)

end General

open MeasureEquivalenceSolenoid

def zeroSumInclusion : zeroSumSpace →+ CompactSequences :=
  l1Embedding.comp zeroSumSpace.toAddSubgroup.subtype

theorem zeroSumInclusion_continuous : Continuous zeroSumInclusion :=
  l1Embedding_continuous.comp continuous_subtype_val

section ActualAction

variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]

def zeroSumRoot (h : zeroSumSpace) : Lp ℝ 2 M :=
  root (orbit M (Multiplicative.ofAdd (zeroSumInclusion h)) : Measure Z) M

/-- The intrinsic l1 topology makes the actual square-root densities continuous
whenever the zero-sum subgroup preserves the measure class. -/
theorem zeroSumRoot_continuous
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M) :
    Continuous (zeroSumRoot M) := by
  letI : PolishSpace (Multiplicative CompactSequences) :=
    inferInstanceAs (PolishSpace CompactSequences)
  letI := upgradeIsCompletelyMetrizable (Multiplicative CompactSequences)
  letI : PolishSpace (Multiplicative zeroSumSpace) :=
    inferInstanceAs (PolishSpace zeroSumSpace)
  letI : MeasurableSpace (Multiplicative zeroSumSpace) := borel (Multiplicative zeroSumSpace)
  letI : BorelSpace (Multiplicative zeroSumSpace) := ⟨rfl⟩
  let i : Multiplicative zeroSumSpace →* Multiplicative CompactSequences :=
    AddMonoidHom.toMultiplicative zeroSumInclusion
  have hi : Continuous i := zeroSumInclusion_continuous
  have hm (h : Multiplicative zeroSumSpace) : i h ∈ quasiInvariantSubgroup M :=
    hQI _ ⟨h.toAdd, h.toAdd.property, rfl⟩
  exact continuous_root_of_mem M i hi hm

end ActualAction

end MeasureEquivalenceRootContinuity

#print axioms MeasureEquivalenceRootContinuity.continuous_root_of_mem
#print axioms MeasureEquivalenceRootContinuity.zeroSumRoot_continuous
