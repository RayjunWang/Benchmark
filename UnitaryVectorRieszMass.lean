import UnitaryVectorRiesz

open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace CompactlySupported

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def realContinuousCompactSupport (f : C(K, ℝ)) : C_c(K, ℝ) :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

theorem representationVectorMeasure_mass_toReal
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    (representationVectorMeasure π v Set.univ).toReal = ‖v‖ ^ 2 := by
  let oneC : C_c(K, ℝ) := realContinuousCompactSupport 1
  have hone : complexifyCompactSupport oneC = 1 := by
    ext x
    simp [complexifyCompactSupport, oneC, realContinuousCompactSupport]
  have h := representationVectorMeasure_integral π v oneC
  rw [hone, map_one] at h
  simpa [oneC, realContinuousCompactSupport, Measure.real,
    inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

theorem representationVectorMeasure_mass
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    representationVectorMeasure π v Set.univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← representationVectorMeasure_mass_toReal π v]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

def continuousNormSquare (f : C(K, ℂ)) : C(K, ℝ) :=
  ⟨fun x => ‖f x‖ ^ 2, f.continuous.norm.pow 2⟩

theorem complexify_normSquare (f : C(K, ℂ)) :
    complexifyCompactSupport (realContinuousCompactSupport (continuousNormSquare f)) =
      star f * f := by
  ext x
  change ((‖f x‖ ^ 2 : ℝ) : ℂ) = star (f x) * f x
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.normSq_eq_conj_mul_self (z := f x)

theorem representationVectorMeasure_integral_norm_sq
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) = ‖π f v‖ ^ 2 := by
  have h := representationVectorMeasure_integral π v
    (realContinuousCompactSupport (continuousNormSquare f))
  rw [complexify_normSquare, map_mul, map_star] at h
  change (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) =
    (inner ℂ v ((π f).adjoint (π f v))).re at h
  rw [ContinuousLinearMap.adjoint_inner_right] at h
  change (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) =
    RCLike.re (inner ℂ (π f v) (π f v)) at h
  rw [← norm_sq_eq_re_inner] at h
  exact h

end MeasureUnitary

#print axioms MeasureUnitary.representationVectorMeasure_mass
#print axioms MeasureUnitary.representationVectorMeasure_integral_norm_sq
