import UnitaryCyclicSpectralSubspace
import UnitaryCyclicRieszIntertwining

/-! The cyclic spectral theorem for an actual unitary: its closed cyclic
subspace is unitarily equivalent to coordinate multiplication on the
actual finite Riesz vector measure on the fixed circle. -/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def submoduleIsometryOfEq (P Q : Submodule ℂ H) (hPQ : P = Q) : P ≃ₗᵢ[ℂ] Q := by
  subst Q
  exact LinearIsometryEquiv.refl ℂ P

theorem submoduleIsometryOfEq_coe (P Q : Submodule ℂ H) (hPQ : P = Q) (x : P) :
    ((submoduleIsometryOfEq P Q hPQ x : Q) : H) = x := by
  subst Q
  rfl

end
end MeasureUnitary

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

theorem circleCoordinate_norm (z : SpectralCircle) : ‖circleCoordinate z‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using z.property

def spectralCoordinateUnitary (μ : Measure SpectralCircle) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  phaseEquiv μ circleCoordinate circleCoordinate.continuous.measurable circleCoordinate_norm

def unitaryCyclicLpEquiv (U : StrongUnitary H) (v : H) :
    Lp ℂ 2 (unitaryVectorSpectralMeasure U v) ≃ₗᵢ[ℂ] cyclicSpan U v :=
  (representationCyclicLpEquiv (unitaryCircleRepresentation U) v).trans
    (submoduleIsometryOfEq _ _ (representationCyclicSubspace_unitaryCircle_eq U v))

theorem unitaryCyclicLpEquiv_coe (U : StrongUnitary H) (v : H)
    (f : Lp ℂ 2 (unitaryVectorSpectralMeasure U v)) :
    ((unitaryCyclicLpEquiv U v f : cyclicSpan U v) : H) =
      representationVectorLpIsometry (unitaryCircleRepresentation U) v f := by
  change ((submoduleIsometryOfEq _ _ (representationCyclicSubspace_unitaryCircle_eq U v)
    (representationCyclicLpEquiv (unitaryCircleRepresentation U) v f) : cyclicSpan U v) : H) = _
  rw [submoduleIsometryOfEq_coe]
  rfl

theorem unitaryCyclicLpEquiv_intertwines (U : StrongUnitary H) (v : H)
    (f : Lp ℂ 2 (unitaryVectorSpectralMeasure U v)) :
    unitaryCyclicLpEquiv U v (spectralCoordinateUnitary (unitaryVectorSpectralMeasure U v) f) =
      cyclicRestriction U v (unitaryCyclicLpEquiv U v f) := by
  apply Subtype.ext
  change ((unitaryCyclicLpEquiv U v
    (spectralCoordinateUnitary (unitaryVectorSpectralMeasure U v) f) : cyclicSpan U v) : H) =
      U ((unitaryCyclicLpEquiv U v f : cyclicSpan U v) : H)
  rw [unitaryCyclicLpEquiv_coe, unitaryCyclicLpEquiv_coe]
  calc
    representationVectorLpIsometry (unitaryCircleRepresentation U) v
        (spectralCoordinateUnitary (unitaryVectorSpectralMeasure U v) f) =
      representationVectorLpIsometry (unitaryCircleRepresentation U) v
        (continuousMultiplierL2 (unitaryVectorSpectralMeasure U v) circleCoordinate f) := by
          rw [continuousMultiplierL2_phase (unitaryVectorSpectralMeasure U v)
            circleCoordinate circleCoordinate_norm f]
          rfl
    _ = unitaryCircleRepresentation U circleCoordinate
        (representationVectorLpIsometry (unitaryCircleRepresentation U) v f) :=
      representationVectorLpIsometry_intertwines (unitaryCircleRepresentation U) v circleCoordinate f
    _ = U (representationVectorLpIsometry (unitaryCircleRepresentation U) v f) := by
      rw [unitaryCircleRepresentation_coordinate]
      rfl

end
end OperatorCoding

#print axioms OperatorCoding.unitaryCyclicLpEquiv_intertwines
