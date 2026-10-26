import L2LocalizedOperators
import L2ProjectionCommutantNormal

/-! Adjoint and reconstruction identities for actual finite compression.
They transfer normality of the finite multiplication algebra to the
norm comparison needed for individual semifinite matrix coefficients. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem globalize_adjoint (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    (globalizeOperator μ A B hB T).adjoint = globalizeOperator μ B A hA T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change inner ℂ (zeroExtend μ A hA (T.adjoint (restrictMap μ B f))) g =
    inner ℂ f (zeroExtend μ B hB (T (restrictMap μ A g)))
  rw [inner_zeroExtend_restrict, ContinuousLinearMap.adjoint_inner_left]
  calc
    inner ℂ (restrictMap μ B f) (T (restrictMap μ A g)) =
        star (inner ℂ (T (restrictMap μ A g)) (restrictMap μ B f)) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ (zeroExtend μ B hB (T (restrictMap μ A g))) f) := by
      rw [inner_zeroExtend_restrict]
    _ = inner ℂ f (zeroExtend μ B hB (T (restrictMap μ A g))) := inner_conj_symm _ _

theorem localize_adjoint (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    (localizeOperator μ C hC T).adjoint = localizeOperator μ C hC T.adjoint := by
  simp only [localizeOperator, ContinuousLinearMap.adjoint_comp,
    restrict_adjoint μ C hC, zeroExtend_adjoint μ C hC,
    ContinuousLinearMap.comp_assoc]

theorem supported_adjoint (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hin : ∀ f, T (indicatorL2 μ hC f) = T f)
    (hout : ∀ f, indicatorL2 μ hC (T f) = T f) :
    (∀ f, T.adjoint (indicatorL2 μ hC f) = T.adjoint f) ∧
      (∀ f, indicatorL2 μ hC (T.adjoint f) = T.adjoint f) := by
  constructor
  · intro f
    apply ext_inner_left ℂ
    intro g
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_indicatorL2, hout,
      ContinuousLinearMap.adjoint_inner_right]
  · intro f
    apply ext_inner_left ℂ
    intro g
    rw [← inner_indicatorL2, ContinuousLinearMap.adjoint_inner_right, hin,
      ContinuousLinearMap.adjoint_inner_right]

theorem zeroExtend_localize (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hout : ∀ f, indicatorL2 μ hC (T f) = T f)
    (f : Lp ℂ 2 (μ.restrict C)) :
    zeroExtend μ C hC (localizeOperator μ C hC T f) = T (zeroExtend μ C hC f) := by
  change zeroExtend μ C hC (restrictMap μ C (T (zeroExtend μ C hC f))) = _
  rw [zeroExtend_restrict, hout]

theorem finite_supported_norm_adjoint (C : Set X) (hC : MeasurableSet C)
    (hfin : μ C ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hin : ∀ f, T (indicatorL2 μ hC f) = T f)
    (hout : ∀ f, indicatorL2 μ hC (T f) = T f)
    (f : Lp ℂ 2 (μ.restrict C)) :
    ‖T (zeroExtend μ C hC f)‖ = ‖T.adjoint (zeroExtend μ C hC f)‖ := by
  letI : IsFiniteMeasure (μ.restrict C) := ⟨by simpa using lt_top_iff_ne_top.mpr hfin⟩
  have hnormal := projectionCommutant_norm_adjoint (μ.restrict C)
    (localizeOperator μ C hC T) (localize_commutes_indicator μ C hC T hT) f
  rw [localize_adjoint] at hnormal
  have hout' := (supported_adjoint μ C hC T hin hout).2
  rw [← zeroExtend_localize μ C hC T hout f,
    ← zeroExtend_localize μ C hC T.adjoint hout' f,
    zeroExtend_norm, zeroExtend_norm]
  exact hnormal

end
end MeasureEquivalenceL2Restriction

#print axioms MeasureEquivalenceL2Restriction.finite_supported_norm_adjoint
