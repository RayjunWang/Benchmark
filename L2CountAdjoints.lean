import L2MatrixColumns
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual adjoint identities for the coordinate injections and
coefficients, and adjoint transposition of genuine operator matrices. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ]

theorem inner_injection_coefficient (d : D) (f : Lp ℂ 2 μ)
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    inner ℂ (injection μ d f) u = inner ℂ f (coefficient μ d u) := by
  classical
  have hI := L2.integrable_inner (𝕜 := ℂ) (injection μ d f) u
  have hterm (i : D) :
      (∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ) =
        if i = d then inner ℂ f (coefficient μ d u) else 0 := by
    by_cases hi : i = d
    · subst i
      rw [if_pos rfl, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ae_slice_of_ae μ (injection_coe μ d f) d,
        coefficient_coe μ d u] with x hinj hc
      rw [hinj, hc]
      simp [injectionFun]
    · rw [if_neg hi]
      calc
        (∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ) = ∫ _ : X, (0 : ℂ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_slice_of_ae μ (injection_coe μ d f) i] with x hinj
          rw [hinj]
          simp [injectionFun, hi]
        _ = 0 := integral_zero _ _
  calc
    inner ℂ (injection μ d f) u =
        ∑' i : D, ∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ := by
      rw [L2.inner_def, integral_prod_symm _ hI, integral_countable hI.integral_prod_right]
      simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    _ = ∑' i : D, if i = d then inner ℂ f (coefficient μ d u) else 0 := tsum_congr hterm
    _ = inner ℂ f (coefficient μ d u) := by simp

theorem coefficient_adjoint (d : D) :
    (coefficientCLM μ d).adjoint = (injectionLI μ d).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact fun f u => inner_injection_coefficient μ d f u

theorem injection_adjoint (d : D) :
    (injectionLI μ d).toContinuousLinearMap.adjoint = coefficientCLM μ d := by
  rw [← coefficient_adjoint, ContinuousLinearMap.adjoint_adjoint]

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]

/-- The genuine operator coefficient matrix transposes under adjoint. -/
theorem matrixCoefficient_adjoint
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d e : D) :
    (matrixCoefficient μ ν T d e).adjoint = matrixCoefficient ν μ T.adjoint e d := by
  simp only [matrixCoefficient, ContinuousLinearMap.adjoint_comp, injection_adjoint,
    coefficient_adjoint, ContinuousLinearMap.comp_assoc]

/-- Rows of the actual unitary coefficient matrix satisfy the dual
Parseval identity; no separately assumed row-mass premise is used. -/
theorem unitary_row_norm_sq
    (U : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d : D) (f : Lp ℂ 2 ν) :
    (∑' e, ‖(matrixCoefficient μ ν U.toContinuousLinearEquiv.toContinuousLinearMap d e).adjoint f‖ ^ 2) =
      ‖f‖ ^ 2 := by
  simp_rw [matrixCoefficient_adjoint]
  have hAdj : U.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap := U.adjoint_eq_symm
  rw [hAdj]
  exact unitary_inverse_column_norm_sq μ ν U d f

end MeasureEquivalenceL2Coefficients

#print axioms MeasureEquivalenceL2Coefficients.coefficient_adjoint
#print axioms MeasureEquivalenceL2Coefficients.matrixCoefficient_adjoint
#print axioms MeasureEquivalenceL2Coefficients.unitary_row_norm_sq
