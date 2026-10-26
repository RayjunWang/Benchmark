import HellingerSplitMap

/-! Affinity disintegration over the actual invariant sigma algebra.
Exceptional sets may depend on the invariant event; no uncountable
intersection of conull sets is taken. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceErgodicDecomposition

open MeasureEquivalenceHellinger

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] [MeasurableSpace.CountablyGenerated Z]
    (μ : Measure Z) [IsFiniteMeasure μ]

theorem invariantBaseKernel_joint_map_of_ae_invariance (e : Z ≃ᵐ Z)
    (hinv : ∀ s : Set Z, MeasurableSet[invariantSigma (G := G)] s →
      e ⁻¹' s =ᵐ[μ] s) :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ
        (invariantBaseKernel (G := G) μ).map e =
      (μ.map e).map (fun z => (invariantBaseMap (G := G) z,z)) := by
  rw [Measure.compProd_map e.measurable, invariantBaseKernel_joint]
  have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z,z)) :=
    (invariantBaseMap_measurable (G := G)).prodMk measurable_id
  rw [Measure.map_map (measurable_id.prodMap e.measurable) hgraph,
    Measure.map_map hgraph e.measurable]
  change μ.map (fun z => (invariantBaseMap (G := G) z,e z)) =
    μ.map (fun z => (invariantBaseMap (G := G) (e z),e z))
  apply Measure.ext_prod
  intro B C hB hC
  have hp2 : Measurable (fun z : Z => (invariantBaseMap (G := G) (e z),e z)) :=
    ((invariantBaseMap_measurable (G := G)).comp e.measurable).prodMk e.measurable
  rw [Measure.map_apply ((invariantBaseMap_measurable (G := G)).prodMk e.measurable)
      (hB.prod hC),
    Measure.map_apply hp2 (hB.prod hC)]
  apply measure_congr
  have h := hinv (B : Set Z) hB
  rw [Filter.eventuallyEq_set] at h ⊢
  filter_upwards [h] with z hz
  change (z ∈ B ∧ e z ∈ C) ↔ (e z ∈ B ∧ e z ∈ C)
  change (e z ∈ B ↔ z ∈ B) at hz
  rw [hz]

theorem invariantConditionalKernel_affinity (e : Z ≃ᵐ Z)
    (hinv : ∀ s : Set Z, MeasurableSet[invariantSigma (G := G)] s →
      e ⁻¹' s =ᵐ[μ] s) :
    affinity μ (μ.map e) =
      ∫ x, affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map e) ∂μ := by
  let β := μ.map (invariantBaseMap (G := G))
  let κ := invariantBaseKernel (G := G) μ
  let j : Z → InvariantBase G Z × Z := fun z => (invariantBaseMap z,z)
  have hj : Measurable j :=
    (invariantBaseMap_measurable (G := G)).prodMk measurable_id
  have hleft : Function.LeftInverse Prod.snd j := fun _ => rfl
  calc
    affinity μ (μ.map e) = affinity (μ.map j) ((μ.map e).map j) :=
      (affinity_map_leftInverse j hj Prod.snd measurable_snd hleft μ (μ.map e)).symm
    _ = affinity (β ⊗ₘ κ) (β ⊗ₘ κ.map e) := by
      have h1 : β ⊗ₘ κ = μ.map j := invariantBaseKernel_joint μ
      have h2 : β ⊗ₘ κ.map e = (μ.map e).map j :=
        invariantBaseKernel_joint_map_of_ae_invariance μ e hinv
      simp only [h1, h2]
    _ = ∫ x, affinity (κ x) ((κ.map e) x) ∂β := affinity_compProd β κ (κ.map e)
    _ = ∫ x, affinity (κ (invariantBaseMap (G := G) x))
        ((κ.map e) (invariantBaseMap (G := G) x)) ∂μ :=
      integral_map (invariantBaseMap_measurable (G := G)).aemeasurable
        (kernelAffinity_measurable κ (κ.map e)).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [κ, invariantBaseKernel, invariantBaseMap,
          invariantConditionalKernel_apply, Kernel.map_apply _ e.measurable]
        rfl)

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_affinity
