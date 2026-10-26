import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure

/-!
Formal check of the conditional-measure step used in compact averaging.
This file does not claim to formalize the complete nonreducibility proof.
The equivalence relation here is literally mutual absolute continuity.
-/

open MeasureTheory ProbabilityTheory Filter

namespace MeasureEquivalenceResearch

def EquivalentMeasures {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) : Prop := mu ≪ nu ∧ nu ≪ mu

theorem map_base_compProd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsFiniteMeasure mu]
    (kappa : Kernel X Y) [IsFiniteKernel kappa]
    (e : X ≃ᵐ X) (he : MeasurePreserving e mu mu) :
    (mu ⊗ₘ kappa).map (Prod.map e id) =
      mu ⊗ₘ kappa.comap e.symm e.symm.measurable := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (e.measurable.prodMap measurable_id) (hs.prod ht)]
  have hpre : (Prod.map e id) ⁻¹' (s ×ˢ t) = (e ⁻¹' s) ×ˢ t := by
    ext p
    rfl
  rw [hpre, Measure.compProd_apply_prod (e.measurable hs) ht,
    Measure.compProd_apply_prod hs ht]
  simpa only [Kernel.comap_apply, Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage hs
      ((kappa.measurable_coe ht).comp e.symm.measurable)

theorem equivalent_compProd_iff
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (mu : Measure X) [SFinite mu] (kappa eta : Kernel X Y)
    [IsFiniteKernel kappa] [IsFiniteKernel eta] :
    EquivalentMeasures (mu ⊗ₘ kappa) (mu ⊗ₘ eta) ↔
      ∀ᵐ x ∂mu, EquivalentMeasures (kappa x) (eta x) := by
  unfold EquivalentMeasures
  rw [Measure.absolutelyContinuous_compProd_right_iff,
    Measure.absolutelyContinuous_compProd_right_iff]
  exact eventually_and.symm

theorem exact_kernel_cosets
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (mu : Measure G) [IsProbabilityMeasure mu]
    (H : AddSubgroup G) (kappa eta : Kernel G Y)
    [IsFiniteKernel kappa] [IsFiniteKernel eta]
    (g : G)
    (htranslate : ∀ x, eta x = kappa (x - g))
    (hreduction : ∀ x y, EquivalentMeasures (kappa x) (kappa y) ↔ x - y ∈ H) :
    EquivalentMeasures (mu ⊗ₘ eta) (mu ⊗ₘ kappa) ↔ g ∈ H := by
  rw [equivalent_compProd_iff]
  have hpoint : ∀ x, EquivalentMeasures (eta x) (kappa x) ↔ g ∈ H := by
    intro x
    rw [htranslate, hreduction]
    have hx : x - g - x = -g := by abel
    rw [hx, H.neg_mem_iff]
  simp_rw [hpoint]
  simp

theorem exact_quasi_invariance_of_kernel_reduction
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableAdd G]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (mu : Measure G) [IsProbabilityMeasure mu] [Measure.IsAddLeftInvariant mu]
    (H : AddSubgroup G) (kappa : Kernel G Y) [IsFiniteKernel kappa]
    (hreduction : ∀ x y, EquivalentMeasures (kappa x) (kappa y) ↔ x - y ∈ H)
    (g : G) :
    EquivalentMeasures ((mu ⊗ₘ kappa).map (fun p => (g + p.1, p.2)))
      (mu ⊗ₘ kappa) ↔ g ∈ H := by
  change EquivalentMeasures
    ((mu ⊗ₘ kappa).map (Prod.map (MeasurableEquiv.addLeft g) id))
    (mu ⊗ₘ kappa) ↔ g ∈ H
  rw [map_base_compProd mu kappa (MeasurableEquiv.addLeft g)
    (measurePreserving_add_left mu g)]
  apply exact_kernel_cosets mu H kappa _ g _ hreduction
  intro x
  simp [Kernel.comap_apply, sub_eq_add_neg, add_comm]

#print axioms equivalent_compProd_iff
#print axioms exact_kernel_cosets
#print axioms map_base_compProd
#print axioms exact_quasi_invariance_of_kernel_reduction

end MeasureEquivalenceResearch
