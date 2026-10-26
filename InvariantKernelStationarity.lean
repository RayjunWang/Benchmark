import ConditionalFibers
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! A stationary Markov kernel that does not cross invariant sets is
stationary on almost every actual invariant conditional probability. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceErgodicDecomposition

section NoLeak

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (P : Kernel Z Z) [IsMarkovKernel P]

theorem setLIntegral_of_stationary_noLeak
    (hstat : P ∘ₘ μ = μ) (B A : Set Z) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (hleak : ∀ᵐ z ∂μ, ∀ᵐ w ∂P z, w ∈ B ↔ z ∈ B) :
    (∫⁻ z in B, P z A ∂μ) = μ (B ∩ A) := by
  have hp : MeasurableSet {p : Z × Z | p.2 ∈ B ↔ p.1 ∈ B} :=
    (hB.preimage measurable_snd).iff (hB.preimage measurable_fst)
  have hj := Measure.ae_compProd_of_ae_ae hp hleak
  have hsets : B ×ˢ A =ᵐ[μ ⊗ₘ P] univ ×ˢ (B ∩ A) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hj] with p hpb
    simp only [mem_prod, mem_univ, true_and, mem_inter_iff]
    tauto
  calc
    _ = (μ ⊗ₘ P) (B ×ˢ A) := (Measure.compProd_apply_prod hB hA).symm
    _ = (μ ⊗ₘ P) (univ ×ˢ (B ∩ A)) := measure_congr hsets
    _ = ∫⁻ z, P z (B ∩ A) ∂μ := by
      simpa only [Measure.restrict_univ] using
        (Measure.compProd_apply_prod (μ := μ) (κ := P) MeasurableSet.univ (hB.inter hA))
    _ = (P ∘ₘ μ) (B ∩ A) := (Measure.bind_apply (hB.inter hA) P.aemeasurable).symm
    _ = _ := congrArg (fun ν : Measure Z => ν (B ∩ A)) hstat

end NoLeak

section Conditional

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (P : Kernel Z Z) [IsMarkovKernel P]

theorem invariantConditionalKernel_stationary
    (hstat : P ∘ₘ μ = μ)
    (hleak : ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z => g • z) ⁻¹' B = B) →
      ∀ᵐ z ∂μ, ∀ᵐ w ∂P z, w ∈ B ↔ z ∈ B) :
    ∀ᵐ x ∂μ, P ∘ₘ invariantConditionalKernel (G := G) μ x =
      invariantConditionalKernel (G := G) μ x := by
  let β := μ.map (invariantBaseMap (G := G))
  let κ := invariantBaseKernel (G := G) μ
  have hj : β ⊗ₘ (P ∘ₖ κ) = β ⊗ₘ κ := by
    apply Measure.ext_prod
    intro B A hB hA
    have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z,z)) :=
      (invariantBaseMap_measurable (G := G)).prodMk measurable_id
    have hi : (∫⁻ z in B, ∫⁻ w, P w A ∂κ z ∂β) =
        ∫⁻ p in B ×ˢ univ, P p.2 A ∂(β ⊗ₘ κ) := by
      symm
      simpa only [Measure.restrict_univ] using
        (Measure.setLIntegral_compProd (μ := β) (κ := κ)
          ((P.measurable_coe hA).comp measurable_snd) hB MeasurableSet.univ)
    have hright : (β ⊗ₘ κ) (B ×ˢ A) = μ ((B:Set Z) ∩ A) := by
      change ((μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ) _ = _
      rw [invariantBaseKernel_joint, Measure.map_apply hgraph (hB.prod hA)]
      rfl
    rw [Measure.compProd_apply_prod hB hA]
    simp_rw [Kernel.comp_apply' P κ _ hA]
    rw [hi]
    change (∫⁻ p in B ×ˢ univ, P p.2 A ∂(μ.map (invariantBaseMap (G := G))) ⊗ₘ
      invariantBaseKernel (G := G) μ) = _
    have hF : Measurable (fun p : InvariantBase G Z × Z => P p.2 A) :=
      (P.measurable_coe hA).comp measurable_snd
    conv_lhs =>
      rw [invariantBaseKernel_joint,
        Measure.restrict_map hgraph (hB.prod MeasurableSet.univ),
        lintegral_map hF hgraph]
    have hpre : (fun z : Z => (invariantBaseMap (G := G) z,z)) ⁻¹' (B ×ˢ univ) =
        (B:Set Z) := by
      ext z
      change (z ∈ B ∧ z ∈ (univ:Set Z)) ↔ z ∈ B
      simp
    rw [hpre]
    change (∫⁻ z in (B:Set Z), P z A ∂μ) = (β ⊗ₘ κ) (B ×ˢ A)
    exact (setLIntegral_of_stationary_noLeak μ P hstat B A hB.1 hA
      (hleak B hB.1 hB.2)).trans hright.symm
  have hκ : (P ∘ₖ κ) =ᵐ[β] κ := Kernel.ae_eq_of_compProd_eq hj
  have h := ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable hκ
  exact h

end Conditional

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_stationary
