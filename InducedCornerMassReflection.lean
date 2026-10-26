import L2TransportedNorms
import L2IndexShiftCoefficients

/-! A genuine unitary equivalence of induced corner modules preserves
their finite base measures. All coefficients, adjoints and Parseval
sums are those of the given unitary; no matrix field or trace is assumed. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureEquivalenceInducedCorners

open MeasureUnitary MeasureEquivalenceL2Restriction
  MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Transport

noncomputable section

variable {X G : Type*} [MeasurableSpace X] [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)

include hmp in
theorem induced_corner_unitary_mass_eq
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (U : Lp ℂ 2 (cornerMeasure (G := G) μ A) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := G) μ B))
    (hproj : ∀ (s : Set X) (hs : MeasurableSet s)
      (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      U (indicatorL2 (cornerMeasure μ A) (hs.preimage orbitPoint_measurable) u) =
        indicatorL2 (cornerMeasure μ B) (hs.preimage orbitPoint_measurable) (U u))
    (hshift : ∀ (g : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      U (inducedShiftUnitary μ A g u) = inducedShiftUnitary μ B g (U u)) :
    μ A = μ B := by
  let T := U.toContinuousLinearEquiv.toContinuousLinearMap
  have hentry (d e : G) :
      ‖matrixCoefficient (μ.restrict A) (μ.restrict B) T d e
          (restrictedOne μ A hfinA)‖ =
        ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T d e).adjoint
          (restrictedOne μ B hfinB)‖ := by
    apply twisted_coefficient_constant_norm_eq_adjoint μ
      (MeasurableEquiv.smul d) (MeasurableEquiv.smul e) (hmp d) (hmp e)
      A B hA hB hfinA hfinB
    intro s hs f
    exact matrixCoefficient_intertwines_projections (μ.restrict A) (μ.restrict B)
      orbitPoint orbitPoint orbitPoint_measurable orbitPoint_measurable T hproj s hs d e f
  have hcov (d : G) :
      matrixCoefficient (μ.restrict A) (μ.restrict B) T d 1 =
        matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 d⁻¹ := by
    have h := matrixCoefficient_shift_covariance μ A B T hshift d⁻¹ d 1
    simpa only [inv_mul_cancel, mul_one] using h.symm
  have hreal : μ.real A = μ.real B := by
    calc
      μ.real A = ‖restrictedOne μ A hfinA‖ ^ 2 := (restrictedOne_norm_sq μ A hfinA).symm
      _ = ∑' d : G, ‖matrixCoefficient (μ.restrict A) (μ.restrict B) T d 1
          (restrictedOne μ A hfinA)‖ ^ 2 :=
        (unitary_column_norm_sq (μ.restrict A) (μ.restrict B) U 1 _).symm
      _ = ∑' d : G, ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T d 1).adjoint
          (restrictedOne μ B hfinB)‖ ^ 2 := tsum_congr (fun d => by rw [hentry d 1])
      _ = ∑' d : G, ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 d⁻¹).adjoint
          (restrictedOne μ B hfinB)‖ ^ 2 := tsum_congr (fun d => by rw [hcov d])
      _ = ∑' e : G, ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 e).adjoint
          (restrictedOne μ B hfinB)‖ ^ 2 :=
        (Equiv.inv G).tsum_eq (fun e : G =>
          ‖(matrixCoefficient (μ.restrict A) (μ.restrict B) T 1 e).adjoint
            (restrictedOne μ B hfinB)‖ ^ 2)
      _ = ‖restrictedOne μ B hfinB‖ ^ 2 := unitary_row_norm_sq (μ.restrict A) (μ.restrict B) U 1 _
      _ = μ.real B := restrictedOne_norm_sq μ B hfinB
  exact (ENNReal.toReal_eq_toReal_iff' hfinA hfinB).mp hreal

end
end MeasureEquivalenceInducedCorners

#print axioms MeasureEquivalenceInducedCorners.induced_corner_unitary_mass_eq
