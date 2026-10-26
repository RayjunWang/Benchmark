import RestrictedRoots
import ZeroSumDense

/-! Measurable invariant sets persist under the intrinsic Polish group closure.
The proof uses actual restricted measures and the continuity of RN roots;
it does not assume continuity of a Koopman representation. -/

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceDenseInvariance

open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceRootContinuity
open MeasureEquivalenceRestrictedRoots

variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem ae_invariant_of_dense (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M)
    (D : Set G) (hD : Dense D) (s : Set Z) (hs : MeasurableSet s)
    (hinv : ∀ d ∈ D, (fun z => i d • z) ⁻¹' s =ᵐ[M] s) :
    ∀ g : G, (fun z => i g • z) ⁻¹' s =ᵐ[M] s := by
  let F : G → FiniteMeasure Z := fun g =>
    restrictedSquareMeasure M hs (root (orbit M (i g) : Measure Z) M)
  let T : G → FiniteMeasure Z := fun g => finiteOrbit (M.restrict s) (i g)
  have hF : Continuous F :=
    (restrictedSquareMeasure_continuous M hs).comp (continuous_root_of_mem M i hi hmem)
  have hT : Continuous T := (finiteOrbit_continuous (M.restrict s)).comp hi
  have hF_value (g : G) :
      (F g : Measure Z) = (M.map (fun z => i g • z)).restrict s := by
    dsimp only [F, restrictedSquareMeasure]
    rw [squareMeasure_cutRoot]
    exact congrArg (fun ν : Measure Z => ν.restrict s)
      (squareMeasure_root M (orbit M (i g) : Measure Z) (hmem g).1)
  have hEq : F = T := by
    apply Continuous.ext_on hD hF hT
    intro d hd
    apply Subtype.ext
    exact (hF_value d).trans
      ((invariant_iff_restrict_map M hs (MeasurableEquiv.smul (i d))).mp (hinv d hd))
  intro g
  apply (invariant_iff_restrict_map M hs (MeasurableEquiv.smul (i g))).mpr
  exact (hF_value g).symm.trans
    (congrArg (fun ν : FiniteMeasure Z => (ν : Measure Z)) (congrFun hEq g))

/-- A measurable quotient fixed almost everywhere by a dense family is fixed
by every element of the intrinsic Polish group. Countable separation handles
the exceptional sets; no conull set uniform in the whole group is asserted. -/
theorem quotient_fixed_of_dense {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y]
    (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M)
    (D : Set G) (hD : Dense D) (q : Z → Y) (hq : Measurable q)
    (hinv : ∀ d ∈ D, (fun z => q (i d • z)) =ᵐ[M] q) :
    ∀ g : G, (fun z => q (i g • z)) =ᵐ[M] q := by
  intro g
  apply Filter.EventuallyEq.of_forall_separating_preimage MeasurableSet
  intro B hB
  apply ae_invariant_of_dense M i hi hmem D hD (q ⁻¹' B) (hB.preimage hq) _ g
  intro d hd
  rw [Filter.eventuallyEq_set]
  filter_upwards [hinv d hd] with z hz
  change q (i d • z) ∈ B ↔ q z ∈ B
  rw [hz]

end MeasureEquivalenceDenseInvariance

#print axioms MeasureEquivalenceDenseInvariance.ae_invariant_of_dense
#print axioms MeasureEquivalenceDenseInvariance.quotient_fixed_of_dense
