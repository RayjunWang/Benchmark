import HellingerConditional
import HellingerErgodic
import RNGraph

/-! Actual quasi-invariance subgroups of component probabilities and
translation of nonsingular ergodic measures by commuting transformations. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceRNGraph MeasureEquivalenceHellinger

section Components

variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

def componentQI (y : Y) : Subgroup K := quasiInvariantSubgroup (κ y)

theorem mem_componentQI_iff (g : K) (y : Y) :
    g ∈ componentQI κ y ↔
      (κ y).map (fun z => g • z) ≪ κ y ∧ κ y ≪ (κ y).map (fun z => g • z) :=
  mem_quasiInvariantSubgroup_iff (κ y) g

theorem measurableSet_componentQI (g : K) : MeasurableSet {y | g ∈ componentQI κ y} := by
  have ha := Kernel.measurableSet_absolutelyContinuous (κ.map (fun z => g • z)) κ
  have hb := Kernel.measurableSet_absolutelyContinuous κ (κ.map (fun z => g • z))
  have he : {y | g ∈ componentQI κ y} =
      {y | (κ.map (fun z => g • z)) y ≪ κ y} ∩
      {y | κ y ≪ (κ.map (fun z => g • z)) y} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_componentQI_iff,
      Kernel.map_apply _ (measurable_const_smul g)]
  rw [he]
  exact ha.inter hb

end Components

section Commuting

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    (μ : Measure Z) (e : Z ≃ᵐ Z)
    (hcomm : ∀ (g : G) (z : Z), e (g • z) = g • e z)

include hcomm in
theorem nonsingular_map_of_commute
    (hns : ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) (μ.map e) (μ.map e) := by
  intro g
  refine ⟨(hns g).measurable, ?_⟩
  have heq : (μ.map e).map (fun z => g • z) = (μ.map (fun z => g • z)).map e := by
    rw [Measure.map_map (hns g).measurable e.measurable,
      Measure.map_map e.measurable (hns g).measurable]
    congr 1
    funext z
    exact (hcomm g z).symm
  rw [heq]
  exact (hns g).absolutelyContinuous.map e.measurable

include hcomm in
theorem ergodic_map_of_commute
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0) :
    ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z => g • z) ⁻¹' s = s) →
      (μ.map e) s = 0 ∨ (μ.map e) sᶜ = 0 := by
  intro s hs hinv
  have hi : ∀ g : G, (fun z => g • z) ⁻¹' (e ⁻¹' s) = e ⁻¹' s := by
    intro g
    ext z
    change e (g • z) ∈ s ↔ e z ∈ s
    rw [hcomm]
    exact Set.ext_iff.mp (hinv g) (e z)
  have h := herg (e ⁻¹' s) (hs.preimage e.measurable) hi
  simpa only [Measure.map_apply e.measurable hs,
    Measure.map_apply e.measurable hs.compl, Set.preimage_compl] using h

end Commuting

end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.measurableSet_componentQI
#print axioms MeasureEquivalenceRigidity.nonsingular_map_of_commute
#print axioms MeasureEquivalenceRigidity.ergodic_map_of_commute
