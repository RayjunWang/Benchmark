import FiberMultiplicityMeasureCode

/-! Changing a dominating base restricts every support to its actual
Radon–Nikodym support; the multiplicity-layer code retains its measure class. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X]

def rnSupport (μ ρ : Measure X) : Set X := {x | μ.rnDeriv ρ x ≠ 0}

theorem rnSupport_measurable (μ ρ : Measure X) : MeasurableSet (rnSupport μ ρ) :=
  (measurableSet_eq_fun (Measure.measurable_rnDeriv μ ρ) measurable_const).compl

theorem rnSupport_measureClass (μ ρ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hμρ : μ ≪ ρ) : μ ≪ ρ.restrict (rnSupport μ ρ) ∧ ρ.restrict (rnSupport μ ρ) ≪ μ := by
  have heq : ae (ρ.withDensity (μ.rnDeriv ρ)) = ae (ρ.restrict (rnSupport μ ρ)) := by
    ext s
    exact ae_withDensity_iff_ae_restrict (Measure.measurable_rnDeriv μ ρ)
  rw [Measure.withDensity_rnDeriv_eq μ ρ hμρ] at heq
  exact ⟨Measure.ae_le_iff_absolutelyContinuous.mp heq.le,
    Measure.ae_le_iff_absolutelyContinuous.mp heq.symm.le⟩

def supportedFamily (A : ℕ → Set X) (C : Set X) (i : ℕ) : Set X := A i ∩ C

theorem supportedFamily_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (C : Set X) (hC : MeasurableSet C) (i : ℕ) : MeasurableSet (supportedFamily A C i) :=
  (hA i).inter hC

theorem fiberMultiplicity_supportedFamily (A : ℕ → Set X) (C : Set X) (x : X) :
    fiberMultiplicity (supportedFamily A C) x =
      if x ∈ C then fiberMultiplicity A x else 0 := by
  classical
  by_cases hx : x ∈ C <;> simp [fiberMultiplicity,supportedFamily,Set.indicator_apply,hx]

theorem multiplicityLayer_supportedFamily (A : ℕ → Set X) (C : Set X) (n : ℕ) :
    multiplicityLayer (supportedFamily A C) n = multiplicityLayer A n ∩ C := by
  classical
  ext x
  change ((n : ℝ≥0∞) < fiberMultiplicity (supportedFamily A C) x) ↔
    (n : ℝ≥0∞) < fiberMultiplicity A x ∧ x ∈ C
  rw [fiberMultiplicity_supportedFamily]
  by_cases hx : x ∈ C <;> simp [hx]

theorem restrict_measureClass_baseChange (μ ρ : Measure X) (C s : Set X)
    (hs : MeasurableSet s) (hμρ : μ ≪ ρ.restrict C) (hρμ : ρ.restrict C ≪ μ) :
    μ.restrict s ≪ ρ.restrict (s ∩ C) ∧ ρ.restrict (s ∩ C) ≪ μ.restrict s := by
  have h1 := hμρ.restrict s
  have h2 := hρμ.restrict s
  rw [Measure.restrict_restrict hs] at h1 h2
  exact ⟨h1,h2⟩

theorem multiplicityLayerCode_baseChange (μ ρ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ] (A : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (C : Set X) (hC : MeasurableSet C)
    (hμρ : μ ≪ ρ.restrict C) (hρμ : ρ.restrict C ≪ μ)
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ i, w {i} ≠ 0) :
    multiplicityLayerCode μ A w ≪ multiplicityLayerCode ρ (supportedFamily A C) w ∧
      multiplicityLayerCode ρ (supportedFamily A C) w ≪ multiplicityLayerCode μ A w := by
  apply (weightedFiberMeasure_measureClass_iff μ ρ (multiplicityLayer A)
    (multiplicityLayer (supportedFamily A C)) (multiplicityLayer_measurable A hA)
    (multiplicityLayer_measurable (supportedFamily A C) (supportedFamily_measurable A hA C hC))
      w w hw hw).mpr
  intro n
  rw [multiplicityLayer_supportedFamily]
  exact restrict_measureClass_baseChange μ ρ C (multiplicityLayer A n)
    (multiplicityLayer_measurable A hA n) hμρ hρμ

end
end MeasureUnitary

#print axioms MeasureUnitary.rnSupport_measureClass
#print axioms MeasureUnitary.multiplicityLayerCode_baseChange

