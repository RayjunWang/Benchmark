import UnitaryCyclicSubspace
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! Actual finite vector-state Riesz measures for representations of a
commutative continuous-function algebra. This construction is used to
build cyclic spectral measures; no spectral classification is assumed. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace CompactlySupported

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def complexifyCompactSupport (f : C_c(K, ℝ)) : C(K, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

theorem complexifyCompactSupport_add (f g : C_c(K, ℝ)) :
    complexifyCompactSupport (f+g) = complexifyCompactSupport f + complexifyCompactSupport g := by
  ext x
  simp [complexifyCompactSupport]

theorem complexifyCompactSupport_smul (a : ℝ) (f : C_c(K, ℝ)) :
    complexifyCompactSupport (a • f) = (a : ℂ) • complexifyCompactSupport f := by
  ext x
  simp [complexifyCompactSupport, smul_eq_mul]

def representationVectorRealFunctional
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : C_c(K, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ v (π (complexifyCompactSupport f) v)).re
  map_add' f g := by
    rw [complexifyCompactSupport_add, map_add, ContinuousLinearMap.add_apply,
      inner_add_right, Complex.add_re]
  map_smul' a f := by
    rw [complexifyCompactSupport_smul, map_smul, ContinuousLinearMap.smul_apply,
      inner_smul_right]
    simp [Complex.mul_re, smul_eq_mul]

theorem representationVectorRealFunctional_nonneg
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (f : C_c(K, ℝ)) (hf : 0 ≤ f) :
    0 ≤ representationVectorRealFunctional π v f := by
  let g : C(K, ℂ) := ⟨fun x => (Real.sqrt (f x) : ℂ),
    Complex.continuous_ofReal.comp f.continuous.sqrt⟩
  have hfactor : complexifyCompactSupport f = star g * g := by
    ext x
    change (f x : ℂ) = star (Real.sqrt (f x) : ℂ) * (Real.sqrt (f x) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← pow_two, Real.sq_sqrt (hf x)]
  change 0 ≤ (inner ℂ v (π (complexifyCompactSupport f) v)).re
  rw [hfactor, map_mul, map_star]
  change 0 ≤ (inner ℂ v ((π g).adjoint ((π g) v))).re
  rw [ContinuousLinearMap.adjoint_inner_right]
  change 0 ≤ RCLike.re (inner ℂ ((π g) v) ((π g) v))
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact sq_nonneg ‖(π g) v‖

def representationVectorPositiveFunctional
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : C_c(K, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := representationVectorRealFunctional π v
  monotone' := by
    intro f g hfg
    have hnonneg := representationVectorRealFunctional_nonneg π v (g-f) (sub_nonneg.mpr hfg)
    simpa only [map_sub, sub_nonneg] using hnonneg

def representationVectorMeasure
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : Measure K :=
  RealRMK.rieszMeasure (representationVectorPositiveFunctional π v)

instance representationVectorMeasure_finite
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    IsFiniteMeasure (representationVectorMeasure π v) := by
  unfold representationVectorMeasure
  infer_instance

theorem representationVectorMeasure_integral
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C_c(K, ℝ)) :
    (∫ x, f x ∂representationVectorMeasure π v) =
      (inner ℂ v (π (complexifyCompactSupport f) v)).re :=
  RealRMK.integral_rieszMeasure (representationVectorPositiveFunctional π v) f

end
end MeasureUnitary

#print axioms MeasureUnitary.representationVectorMeasure_integral
