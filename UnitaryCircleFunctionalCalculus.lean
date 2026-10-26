import UnitaryVectorRiesz
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! The actual continuous-function representation on one fixed unit
circle supplied by the continuous functional calculus of a unitary. -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal InnerProductSpace CStarAlgebra

set_option maxHeartbeats 1500000

namespace OperatorCoding

noncomputable section

abbrev SpectralCircle := Metric.sphere (0 : ℂ) 1

instance spectralCircle_compact : CompactSpace SpectralCircle :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) 1)

def circleCoordinate : C(SpectralCircle, ℂ) :=
  (ContinuousMap.id ℂ).restrict (Metric.sphere (0 : ℂ) 1)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

local instance : ContinuousFunctionalCalculus ℂ (H →L[ℂ] H) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

theorem strongUnitary_mem_unitary (U : StrongUnitary H) :
    (U : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) :=
  (Unitary.linearIsometryEquiv.symm U).property

theorem strongUnitary_spectrum_circle (U : StrongUnitary H) :
    spectrum ℂ (U : H →L[ℂ] H) ⊆ Metric.sphere (0 : ℂ) 1 := by
  intro z hz
  simpa only [Metric.mem_sphere, dist_zero_right] using
    spectrum.norm_eq_one_of_unitary (strongUnitary_mem_unitary U) hz

def unitaryCircleRepresentation (U : StrongUnitary H) :
    C(SpectralCircle, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  cfcHomSuperset (R := ℂ) (a := (U : H →L[ℂ] H))
    (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U)) (strongUnitary_spectrum_circle U)

theorem unitaryCircleRepresentation_continuous (U : StrongUnitary H) :
    Continuous (unitaryCircleRepresentation U) :=
  cfcHomSuperset_continuous (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U))
    (strongUnitary_spectrum_circle U)

theorem unitaryCircleRepresentation_norm_le (U : StrongUnitary H) (f : C(SpectralCircle, ℂ)) :
    ‖unitaryCircleRepresentation U f‖ ≤ ‖f‖ := by
  unfold unitaryCircleRepresentation cfcHomSuperset
  rw [StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply,
    norm_cfcHom (U : H →L[ℂ] H) _ (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U))]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact ContinuousMap.norm_coe_le_norm f _

theorem unitaryCircleRepresentation_coordinate (U : StrongUnitary H) :
    unitaryCircleRepresentation U circleCoordinate = (U : H →L[ℂ] H) :=
  cfcHomSuperset_id (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U))
    (strongUnitary_spectrum_circle U)

theorem unitaryCircleRepresentation_coordinate_pow (U : StrongUnitary H) (n : ℕ) :
    unitaryCircleRepresentation U (circleCoordinate ^ n) = (U : H →L[ℂ] H) ^ n := by
  rw [map_pow, unitaryCircleRepresentation_coordinate]

theorem unitaryCircleRepresentation_star_coordinate (U : StrongUnitary H) :
    unitaryCircleRepresentation U (star circleCoordinate) = (U : H →L[ℂ] H).adjoint := by
  rw [map_star, unitaryCircleRepresentation_coordinate, ContinuousLinearMap.star_eq_adjoint]

def unitaryVectorSpectralMeasure (U : StrongUnitary H) (v : H) : Measure SpectralCircle :=
  MeasureUnitary.representationVectorMeasure (unitaryCircleRepresentation U) v

instance unitaryVectorSpectralMeasure_finite (U : StrongUnitary H) (v : H) :
    IsFiniteMeasure (unitaryVectorSpectralMeasure U v) := by
  unfold unitaryVectorSpectralMeasure
  infer_instance

end
end OperatorCoding

#print axioms OperatorCoding.unitaryCircleRepresentation_coordinate
#print axioms OperatorCoding.unitaryVectorSpectralMeasure
