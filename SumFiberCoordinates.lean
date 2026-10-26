import FiberEventRepresentative

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def sumFiberEquiv (n : ℕ) (α : Type*) [MeasurableSpace α] :
    ((Fin (n + 1) → ℝ) × α) ≃ᵐ ((ℝ × α) × (Fin n → ℝ)) :=
  ((sumTailEquiv n).prodCongr (MeasurableEquiv.refl α)).trans
    (MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc.symm))

@[simp] theorem sumFiberEquiv_apply (n : ℕ) {α : Type*} [MeasurableSpace α]
    (x : (Fin (n + 1) → ℝ) × α) :
    sumFiberEquiv n α x = ((∑ i, x.1 i, x.2), fun i => x.1 i.succ) := rfl

@[simp] theorem sumFiberEquiv_symm_apply (n : ℕ) {α : Type*} [MeasurableSpace α]
    (x : (ℝ × α) × (Fin n → ℝ)) :
    (sumFiberEquiv n α).symm x = (Fin.cons (x.1.1 - ∑ i, x.2 i) x.2, x.1.2) := rfl

theorem measurePreserving_sumFiberEquiv (n : ℕ) {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] :
    MeasurePreserving (sumFiberEquiv n α)
      ((volume : Measure (Fin (n + 1) → ℝ)).prod μ)
      (((volume : Measure ℝ).prod μ).prod (volume : Measure (Fin n → ℝ))) := by
  have h₁ := (measurePreserving_sumTailEquiv n).prod (MeasurePreserving.id μ)
  have h₂ := measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure (Fin n → ℝ)) μ
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ))) (ν := μ))
  have h₄ := (measurePreserving_prodAssoc (volume : Measure ℝ) μ
    (volume : Measure (Fin n → ℝ))).symm MeasurableEquiv.prodAssoc
  exact h₄.comp (h₃.comp (h₂.comp h₁))

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.measurePreserving_sumFiberEquiv
