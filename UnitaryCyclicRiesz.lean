import UnitaryVectorRieszMass
import MeasureUnitaryDensity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.Extend

open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace

set_option maxHeartbeats 1200000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationVectorLinearMap (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    C(K, ℂ) →ₗ[ℂ] H where
  toFun f := π f v
  map_add' f g := by simp
  map_smul' c f := by simp

theorem representationVector_norm_toLp
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    ‖π f v‖ = ‖ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f‖ := by
  have h := representationVectorMeasure_integral_norm_sq π v f
  have he : (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) =
      ‖ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) (representationVectorMeasure π v)] with x hx
    rw [hx]
  nlinarith [norm_nonneg (π f v),
    norm_nonneg (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f)]

instance representationVectorMeasure_weaklyRegular
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    (representationVectorMeasure π v).WeaklyRegular := by
  unfold representationVectorMeasure
  infer_instance

def representationVectorLpOperator
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) →L[ℂ] H :=
  (representationVectorLinearMap π v).extendOfNorm
    (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ).toLinearMap

theorem representationVectorLpOperator_toLp
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    representationVectorLpOperator π v
      (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f) = π f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  · refine ⟨1, fun g => ?_⟩
    simpa only [one_mul] using (representationVector_norm_toLp π v g).le

theorem representationVectorLpOperator_norm
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    ‖representationVectorLpOperator π v f‖ = ‖f‖ := by
  have hd := ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  refine hd.induction ?_ ?_ f
  · rintro z ⟨g, rfl⟩
    rw [representationVectorLpOperator_toLp]
    exact representationVector_norm_toLp π v g
  · exact isClosed_eq (continuous_norm.comp (representationVectorLpOperator π v).continuous) continuous_norm

def representationVectorLpIsometry
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) →ₗᵢ[ℂ] H where
  __ := (representationVectorLpOperator π v).toLinearMap
  norm_map' := representationVectorLpOperator_norm π v

end MeasureUnitary

#print axioms MeasureUnitary.representationVectorLpIsometry
