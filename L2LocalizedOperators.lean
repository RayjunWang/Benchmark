import L2RestrictionExtension
import L2ModuleCommutant

/-! Actual globalization and finite-measure localization of L2 module
operators, reducing a semifinite supported operator to the proved finite
measure multiplier theorem. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem restrict_indicator (A s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    restrictMap μ A (indicatorL2 μ hs f) =
      indicatorL2 (μ.restrict A) hs (restrictMap μ A f) := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (indicatorL2 μ hs f), restrict_coe μ A f,
    ae_restrict_of_ae (indicatorL2_coe μ hs f),
    indicatorL2_coe (μ.restrict A) hs (restrictMap μ A f)] with x hr hf hi ho
  rw [hr, hi, ho]
  by_cases hx : x ∈ s <;> simp [hx, hf]

theorem zeroExtend_indicator (A : Set X) (hA : MeasurableSet A)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA (indicatorL2 (μ.restrict A) hs f) =
      indicatorL2 μ hs (zeroExtend μ A hA f) := by
  apply Lp.ext
  have hsrc := (ae_eq_restrict_iff_indicator_ae_eq hA).mp
    (indicatorL2_coe (μ.restrict A) hs f)
  filter_upwards [zeroExtend_coe μ A hA (indicatorL2 (μ.restrict A) hs f),
    zeroExtend_coe μ A hA f, indicatorL2_coe μ hs (zeroExtend μ A hA f), hsrc]
    with x he hf hi hsource
  rw [he, hi, hsource]
  by_cases hxA : x ∈ A <;> by_cases hxs : x ∈ s <;> simp [hxA, hxs, hf] at *

/-- Extend an actual operator between two restricted L2 spaces to the
ambient L2 space, by bounded restriction and genuine zero extension. -/
def globalizeOperator (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (zeroExtendLI μ B hB).toContinuousLinearMap.comp (T.comp (restrictCLM μ A))

theorem globalize_input_supported (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    globalizeOperator μ A B hB T (indicatorL2 μ hA f) = globalizeOperator μ A B hB T f := by
  change zeroExtend μ B hB (T (restrictMap μ A (indicatorL2 μ hA f))) =
    zeroExtend μ B hB (T (restrictMap μ A f))
  rw [← zeroExtend_restrict μ A hA f, restrict_zeroExtend]

theorem globalize_output_supported (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    indicatorL2 μ hB (globalizeOperator μ A B hB T f) = globalizeOperator μ A B hB T f := by
  change indicatorL2 μ hB (zeroExtend μ B hB (T (restrictMap μ A f))) =
    zeroExtend μ B hB (T (restrictMap μ A f))
  rw [← zeroExtend_restrict, restrict_zeroExtend]

theorem globalize_commutes_indicator (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) hs f) = indicatorL2 (μ.restrict B) hs (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    globalizeOperator μ A B hB T (indicatorL2 μ hs f) =
      indicatorL2 μ hs (globalizeOperator μ A B hB T f) := by
  change zeroExtend μ B hB (T (restrictMap μ A (indicatorL2 μ hs f))) =
    indicatorL2 μ hs (zeroExtend μ B hB (T (restrictMap μ A f)))
  rw [restrict_indicator, hT, zeroExtend_indicator]

/-- Actual compression of an ambient L2 operator to a measurable set. -/
def localizeOperator (C : Set X) (hC : MeasurableSet C) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 (μ.restrict C) →L[ℂ] Lp ℂ 2 (μ.restrict C) :=
  (restrictCLM μ C).comp (T.comp (zeroExtendLI μ C hC).toContinuousLinearMap)

theorem localize_commutes_indicator (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict C)) :
    localizeOperator μ C hC T (indicatorL2 (μ.restrict C) hs f) =
      indicatorL2 (μ.restrict C) hs (localizeOperator μ C hC T f) := by
  change restrictMap μ C (T (zeroExtend μ C hC (indicatorL2 (μ.restrict C) hs f))) =
    indicatorL2 (μ.restrict C) hs (restrictMap μ C (T (zeroExtend μ C hC f)))
  rw [zeroExtend_indicator, hT, restrict_indicator]

/-- The supported semifinite matrix coefficient is reduced to the
actual finite-measure multiplier theorem on C. -/
theorem exists_localized_multiplier (C : Set X) (hC : MeasurableSet C) (hfin : μ C ≠ ∞)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∃ b : Lp ℂ ∞ (μ.restrict C), localizeOperator μ C hC T = boundedMultiplierL2 (μ.restrict C) b := by
  letI : IsFiniteMeasure (μ.restrict C) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (lt_top_iff_ne_top.mpr hfin)⟩
  have hc := localize_commutes_indicator μ C hC T hT
  exact ⟨projectionCommutantSymbol (μ.restrict C) (localizeOperator μ C hC T) hc,
    projectionCommutant_eq_multiplier (μ.restrict C) (localizeOperator μ C hC T) hc⟩

end
end MeasureEquivalenceL2Restriction

#print axioms MeasureEquivalenceL2Restriction.globalizeOperator
#print axioms MeasureEquivalenceL2Restriction.globalize_commutes_indicator
#print axioms MeasureEquivalenceL2Restriction.exists_localized_multiplier
