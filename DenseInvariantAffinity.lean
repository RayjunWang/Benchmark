import InvariantAffinity
import DenseInvariantSets

/-! The true affinity formula for every element of an intrinsic Polish
group, after conditioning on a dense subgroup's invariant sigma algebra. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceDenseInvariance

open MeasureEquivalenceDensity MeasureEquivalenceRNGraph
  MeasureEquivalenceErgodicDecomposition MeasureEquivalenceHellinger

variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M)
    (D : Subgroup G) (hD : Dense (D : Set G))

include hi hmem hD in
theorem denseInvariant_affinity (g : G) :
    letI : MulAction D Z := MulAction.compHom Z (i.comp D.subtype)
    affinity M (M.map (fun z => i g • z)) =
      ∫ x, affinity (invariantConditionalKernel (G := D) M x)
        ((invariantConditionalKernel (G := D) M x).map (fun z => i g • z)) ∂M := by
  letI : MulAction D Z := MulAction.compHom Z (i.comp D.subtype)
  apply invariantConditionalKernel_affinity M (MeasurableEquiv.smul (i g))
  intro s hs
  apply ae_invariant_of_dense M i hi hmem (D : Set G) hD s hs.1 _ g
  intro d hd
  apply EventuallyEq.of_eq
  exact hs.2 ⟨d,hd⟩

end MeasureEquivalenceDenseInvariance

#print axioms MeasureEquivalenceDenseInvariance.denseInvariant_affinity
