import ZeroSumConditional
import ComponentRigidityRoots

/-! Actual zero-sum quasi-invariance rigidity. Every summable shift
preserves the measure class as soon as every zero-sum summable shift does. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceRigidity

noncomputable section

open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
  MeasureEquivalenceRNGraph MeasureEquivalenceHellinger
  MeasureEquivalenceErgodicDecomposition

def coordinateShiftHom : ℝ →+ Additive (Multiplicative CompactSequences) where
  toFun a := Additive.ofMul (Multiplicative.ofAdd (coordinateShift a))
  map_zero' := by
    change coordinateShift 0 = 0
    simp [coordinateShift]
  map_add' a b := by
    change coordinateShift (a+b) = coordinateShift a + coordinateShift b
    simp [coordinateShift, lp.single_add]

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)

include hQI in
theorem coordinateShift_quasiInvariant (a : ℝ) :
    Multiplicative.ofAdd (coordinateShift a) ∈ quasiInvariantSubgroup M := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure M
  letI : MulAction rationalZeroSumGroup Z := rationalZeroSumAction
  letI : MeasurableConstSMul rationalZeroSumGroup Z := ⟨fun d =>
    measurable_const_smul (zeroSumGroupHom d.val)⟩
  have hns (d : rationalZeroSumGroup) :
      QuasiMeasurePreserving (fun z : Z => d • z) M M := by
    refine ⟨measurable_const_smul d, ?_⟩
    exact (hQI _ ⟨d.val.toAdd,d.val.toAdd.property,rfl⟩).1
  have hcomm (k : Multiplicative CompactSequences) (d : rationalZeroSumGroup) (z : Z) :
      k • (d • z) = d • (k • z) := by
    change k • (zeroSumGroupHom d.val • z) = zeroSumGroupHom d.val • (k • z)
    exact smul_comm k _ z
  exact quasiInvariant_of_uniform_invariant_mean_affinity M hns coordinateShiftHom hcomm
    (zeroSumComponentKernel_coordinate_mean M hQI) a

include hQI in
theorem zeroSum_quasiInvariant_rigidity :
    ∀ h : CompactSequences, h ∈ summableSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M := by
  rintro h ⟨u,rfl⟩
  obtain ⟨z,hz,he⟩ := decompose_l1 u
  have h1 := hQI z hz
  have h2 := coordinateShift_quasiInvariant M hQI (∑' n,u n)
  have hm := (quasiInvariantSubgroup M).mul_mem h1 h2
  change Multiplicative.ofAdd (z + coordinateShift (∑' n,u n)) ∈ quasiInvariantSubgroup M at hm
  rwa [← he] at hm

end
end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.coordinateShift_quasiInvariant
#print axioms MeasureEquivalenceRigidity.zeroSum_quasiInvariant_rigidity
