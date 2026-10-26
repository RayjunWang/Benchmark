import L2MatrixProjection
import InducedCornerUnitary

/-! Actual matrix-coefficient covariance follows directly from a genuine
intertwiner of the left counting-coordinate shifts. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 800000

namespace MeasureEquivalenceL2Coefficients

open MeasureEquivalenceInducedCorners MeasureUnitary

noncomputable section

variable {X G : Type*} [MeasurableSpace X] [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SigmaFinite μ]

theorem coefficient_inducedShift (A : Set X) (g d : G)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    coefficient (μ.restrict A) d (inducedShiftUnitary μ A g u) =
      coefficient (μ.restrict A) (g⁻¹*d) u := by
  apply Lp.ext
  filter_upwards [coefficient_coe (μ.restrict A) d (inducedShiftUnitary μ A g u),
    ae_slice_of_ae (μ.restrict A) (inducedShiftUnitary_coe μ A g u) d,
    coefficient_coe (μ.restrict A) (g⁻¹*d) u] with x hc hs hu
  exact hc.trans (hs.trans hu.symm)

theorem inducedShift_injection (A : Set X) (g e : G) (f : Lp ℂ 2 (μ.restrict A)) :
    inducedShiftUnitary μ A g (injection (μ.restrict A) e f) =
      injection (μ.restrict A) (g*e) f := by
  classical
  apply coefficient_ext (μ.restrict A)
  intro d
  rw [coefficient_inducedShift]
  simp only [coefficient_injection]
  have he : g⁻¹*d = e ↔ d = g*e := by
    constructor
    · intro h
      rw [← h, mul_inv_cancel_left]
    · rintro rfl
      exact inv_mul_cancel_left g e
  exact if_congr he rfl rfl

theorem matrixCoefficient_shift_covariance (A B : Set X)
    (T : Lp ℂ 2 (cornerMeasure (G := G) μ A) →L[ℂ]
      Lp ℂ 2 (cornerMeasure (G := G) μ B))
    (hT : ∀ (g : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      T (inducedShiftUnitary μ A g u) = inducedShiftUnitary μ B g (T u))
    (g d e : G) :
    matrixCoefficient (μ.restrict A) (μ.restrict B) T (g*d) (g*e) =
      matrixCoefficient (μ.restrict A) (μ.restrict B) T d e := by
  apply ContinuousLinearMap.ext
  intro f
  change coefficient (μ.restrict B) (g*d) (T (injection (μ.restrict A) (g*e) f)) = _
  rw [← inducedShift_injection μ A g e f, hT,
    coefficient_inducedShift, inv_mul_cancel_left]
  rfl

end
end MeasureEquivalenceL2Coefficients

#print axioms MeasureEquivalenceL2Coefficients.matrixCoefficient_shift_covariance
