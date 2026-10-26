import FiberMultiplicityClassification

/-! Canonical multiplicity layers recover the finite-or-countable rank. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

def multiplicityLayer (A : ℕ → Set X) (n : ℕ) : Set X :=
  {x | (n : ℝ≥0∞) < fiberMultiplicity A x}

theorem multiplicityLayer_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    MeasurableSet (multiplicityLayer A n) :=
  measurableSet_lt measurable_const (fiberMultiplicity_measurable A hA)

theorem enat_eq_of_natCuts (a b : ℕ∞)
    (h : ∀ n : ℕ, (n : ℕ∞) < a ↔ (n : ℕ∞) < b) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe n => exact False.elim ((lt_irrefl (n : ℕ∞)) ((h n).mp (ENat.coe_lt_top n)))
  | coe m =>
    induction b using ENat.recTopCoe with
    | top => exact False.elim ((lt_irrefl (m : ℕ∞)) ((h m).mpr (ENat.coe_lt_top m)))
    | coe n =>
      congr 1
      apply le_antisymm
      · by_contra hmn
        have hlt : (n : ℕ∞) < (m : ℕ∞) := ENat.coe_lt_coe.mpr (lt_of_not_ge hmn)
        exact (lt_irrefl (n : ℕ∞)) ((h n).mp hlt)
      · by_contra hnm
        have hlt : (m : ℕ∞) < (n : ℕ∞) := ENat.coe_lt_coe.mpr (lt_of_not_ge hnm)
        exact (lt_irrefl (m : ℕ∞)) ((h m).mpr hlt)

theorem fiberMultiplicity_eq_of_layers (A B : ℕ → Set X) (x : X)
    (h : ∀ n, x ∈ multiplicityLayer A n ↔ x ∈ multiplicityLayer B n) :
    fiberMultiplicity A x = fiberMultiplicity B x := by
  have hc : {i : ℕ | x ∈ A i}.encard = {i : ℕ | x ∈ B i}.encard := by
    apply enat_eq_of_natCuts
    intro n
    have hn := h n
    change (n : ℝ≥0∞) < fiberMultiplicity A x ↔ (n : ℝ≥0∞) < fiberMultiplicity B x at hn
    rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard] at hn
    simpa only [← ENat.toENNReal_coe n, ENat.toENNReal_lt] using hn
  rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard, hc]

theorem restrict_measureClass_iff_ae (μ : Measure X) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ.restrict s ≪ μ.restrict t ∧ μ.restrict t ≪ μ.restrict s) ↔ s =ᵐ[μ] t := by
  constructor
  · rintro ⟨hst,hts⟩
    have hst' := ae_imp_of_ae_restrict ((Measure.AbsolutelyContinuous.ae_le hst) (ae_restrict_mem ht))
    have hts' := ae_imp_of_ae_restrict ((Measure.AbsolutelyContinuous.ae_le hts) (ae_restrict_mem hs))
    filter_upwards [hst',hts'] with x hx hy
    exact propext ⟨hx,hy⟩
  · intro hst
    have heq : μ.restrict s = μ.restrict t := Measure.restrict_congr_set hst
    rw [heq]
    exact ⟨Measure.AbsolutelyContinuous.rfl,Measure.AbsolutelyContinuous.rfl⟩

theorem multiplicityLayer_measureClass_iff (μ : Measure X) (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (∀ n, μ.restrict (multiplicityLayer A n) ≪ μ.restrict (multiplicityLayer B n) ∧
      μ.restrict (multiplicityLayer B n) ≪ μ.restrict (multiplicityLayer A n)) ↔
        fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  constructor
  · intro h
    have hcuts (n : ℕ) : multiplicityLayer A n =ᵐ[μ] multiplicityLayer B n :=
      (restrict_measureClass_iff_ae μ _ _ (multiplicityLayer_measurable A hA n)
        (multiplicityLayer_measurable B hB n)).mp (h n)
    filter_upwards [ae_all_iff.mpr hcuts] with x hx
    exact fiberMultiplicity_eq_of_layers A B x (fun n => (hx n).to_iff)
  · intro h n
    apply (restrict_measureClass_iff_ae μ _ _ (multiplicityLayer_measurable A hA n)
      (multiplicityLayer_measurable B hB n)).mpr
    filter_upwards [h] with x hx
    change ((n : ℝ≥0∞) < fiberMultiplicity A x) = ((n : ℝ≥0∞) < fiberMultiplicity B x)
    rw [hx]

end
end MeasureUnitary

#print axioms MeasureUnitary.multiplicityLayer_measureClass_iff

