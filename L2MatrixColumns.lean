import L2CountInjections

/-! The column norm identities of a genuine isometry on the actual
product L2 space, without an assumed pointwise matrix or semifinite trace. -/

open MeasureTheory
open scoped ENNReal

namespace MeasureEquivalenceL2Coefficients

variable {X Y D : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Y) [SigmaFinite ν]

theorem unitary_column_norm_sq
    (U : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (e : D) (f : Lp ℂ 2 μ) :
    (∑' d, ‖matrixCoefficient μ ν U.toContinuousLinearEquiv.toContinuousLinearMap d e f‖ ^ 2) =
      ‖f‖ ^ 2 := by
  change (∑' d, ‖coefficient ν d (U (injection μ e f))‖ ^ 2) = ‖f‖ ^ 2
  rw [← norm_sq_eq_tsum_coefficient_norm_sq, U.norm_map, injection_norm]

theorem unitary_inverse_column_norm_sq
    (U : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d : D) (f : Lp ℂ 2 ν) :
    (∑' e, ‖matrixCoefficient ν μ U.symm.toContinuousLinearEquiv.toContinuousLinearMap e d f‖ ^ 2) =
      ‖f‖ ^ 2 :=
  unitary_column_norm_sq ν μ U.symm d f

end MeasureEquivalenceL2Coefficients

#print axioms MeasureEquivalenceL2Coefficients.unitary_column_norm_sq
#print axioms MeasureEquivalenceL2Coefficients.unitary_inverse_column_norm_sq
