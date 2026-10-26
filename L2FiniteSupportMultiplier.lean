import L2RestrictionExtension
import L2ModuleCommutant

/-! A finite-supported projection-commuting operator on an arbitrary L²
space is an actual bounded multiplier on its finite support. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem restrict_indicator_support (C s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    restrictMap μ C (indicatorL2 μ hs f) =
      indicatorL2 (μ.restrict C) hs (restrictMap μ C f) := by
  apply Lp.ext
  filter_upwards [restrict_coe μ C (indicatorL2 μ hs f),
    ae_restrict_of_ae (indicatorL2_coe μ hs f),
    indicatorL2_coe (μ.restrict C) hs (restrictMap μ C f), restrict_coe μ C f]
    with x hr hi ho hf
  rw [hr,hi,ho]
  by_cases hx : x ∈ s <;> simp [hx,hf]

private theorem zeroExtend_indicator_support (C : Set X) (hC : MeasurableSet C)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict C)) :
    zeroExtend μ C hC (indicatorL2 (μ.restrict C) hs f) =
      indicatorL2 μ hs (zeroExtend μ C hC f) := by
  apply Lp.ext
  have hi := (ae_eq_restrict_iff_indicator_ae_eq hC).mp
    (indicatorL2_coe (μ.restrict C) hs f)
  filter_upwards [zeroExtend_coe μ C hC (indicatorL2 (μ.restrict C) hs f),
    indicatorL2_coe μ hs (zeroExtend μ C hC f),zeroExtend_coe μ C hC f,hi]
    with x hleft hright he hi
  rw [hleft,hright]
  by_cases hxC : x ∈ C
  · simp only [indicator_of_mem hxC] at hi ⊢
    by_cases hxs : x ∈ s <;> simp [hxs,he,hi,hxC]
  · by_cases hxs : x ∈ s <;> simp [hxC,hxs,he]

def finiteCompression (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 (μ.restrict C) →L[ℂ] Lp ℂ 2 (μ.restrict C) :=
  (restrictCLM μ C).comp (T.comp (zeroExtendLI μ C hC).toContinuousLinearMap)

theorem finiteCompression_commutes (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict C)),
      finiteCompression μ C hC T (indicatorL2 (μ.restrict C) hs f) =
        indicatorL2 (μ.restrict C) hs (finiteCompression μ C hC T f) := by
  intro s hs f
  change restrictMap μ C (T (zeroExtend μ C hC (indicatorL2 (μ.restrict C) hs f))) = _
  rw [zeroExtend_indicator_support,hT,restrict_indicator_support]
  rfl

theorem exists_finite_support_multiplier (C : Set X) (hC : MeasurableSet C)
    (hfinite : μ C < ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hsource : ∀ f, T (indicatorL2 μ hC f) = T f)
    (htarget : ∀ f, indicatorL2 μ hC (T f) = T f) :
    ∃ b : Lp ℂ ∞ (μ.restrict C), ∀ f : Lp ℂ 2 μ,
      T f =ᵐ[μ] C.indicator (fun x => b x * f x) := by
  letI : IsFiniteMeasure (μ.restrict C) := ⟨by simpa using hfinite⟩
  let S := finiteCompression μ C hC T
  have hS := finiteCompression_commutes μ C hC T hT
  let b := projectionCommutantSymbol (μ.restrict C) S hS
  have hSm : S = boundedMultiplierL2 (μ.restrict C) b :=
    projectionCommutant_eq_multiplier (μ.restrict C) S hS
  refine ⟨b,?_⟩
  intro f
  have hreconstruct : zeroExtend μ C hC (S (restrictMap μ C f)) = T f := by
    change zeroExtend μ C hC (restrictMap μ C (T (zeroExtend μ C hC (restrictMap μ C f)))) = _
    rw [zeroExtend_restrict,zeroExtend_restrict,hsource,htarget]
  rw [← hreconstruct]
  have hcoeff : S (restrictMap μ C f) =ᵐ[μ.restrict C] fun x => b x * f x := by
    rw [hSm]
    filter_upwards [boundedMultiplierL2_coe (μ.restrict C) b (restrictMap μ C f),
      restrict_coe μ C f] with x hm hr
    rw [hm,hr]
  exact (zeroExtend_coe μ C hC (S (restrictMap μ C f))).trans
    ((ae_eq_restrict_iff_indicator_ae_eq hC).mp hcoeff)

end
end MeasureEquivalenceL2Restriction

#print axioms MeasureEquivalenceL2Restriction.exists_finite_support_multiplier
