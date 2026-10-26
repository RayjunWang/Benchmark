import RestrictedDensity
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem infinitePi_sum {α β : Type*} (μ : α → Measure ℝ) (ν : β → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm =
      Measure.infinitePi (Sum.elim μ ν) := by
  letI (i : α ⊕ β) : IsProbabilityMeasure (Sum.elim μ ν i) := by
    cases i <;> dsimp <;> infer_instance
  apply Measure.eq_infinitePi
  intro s t ht
  have hpre : (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm ⁻¹'
      Set.pi s t = Set.pi s.toLeft (fun i => t (.inl i)) ×ˢ
        Set.pi s.toRight (fun j => t (.inr j)) := by
    ext z
    simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi,
      Set.mem_pi, Sum.forall]
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable
    (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i)), hpre,
    Measure.prod_prod,
    Measure.infinitePi_pi μ (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi ν (fun j _ => ht (.inr j))]
  exact (Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight s
    (fun i => Sum.elim μ ν i (t i))).symm

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.infinitePi_sum
