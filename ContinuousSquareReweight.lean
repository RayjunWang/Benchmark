import DensityInverseContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def continuousSquareReweight (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) : PositiveCylinderProbabilities :=
  densityTarget (positiveContinuousSection w hw μ)

theorem continuous_continuousSquareReweight (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    Continuous (continuousSquareReweight w hw) :=
  continuous_densityTarget.comp (continuous_positiveContinuousSection w hw)

theorem densityVector_section_coe (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) :
    densityVector (positiveContinuousSection w hw μ) =ᵐ[
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      fun x => ‖continuousDensityVector μ w‖⁻¹ * w x := by
  have hLift : densityVector (positiveContinuousSection w hw μ) = normalizedContinuousVector μ w :=
    (cantorRealHaarBasis μ).repr.symm_apply_apply _
  rw [hLift]
  filter_upwards [Lp.coeFn_smul ‖continuousDensityVector μ w‖⁻¹ (continuousDensityVector μ w),
    continuousDensityVector_coe μ w] with x hx hy
  simpa only [normalizedContinuousVector, Pi.smul_apply, smul_eq_mul, hy] using hx

theorem continuousSquareReweight_measure (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) :
    ((continuousSquareReweight w hw μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
        (fun x => ENNReal.ofReal ((‖continuousDensityVector μ w‖⁻¹ * w x) ^ 2)) := by
  apply withDensity_congr_ae
  filter_upwards [densityVector_section_coe w hw μ] with x hx
  rw [hx]

theorem continuousSquareReweight_inverse (w v : C(HaarCantor, ℝ))
    (hw : ∀ x, 0 < w x) (hv : ∀ x, 0 < v x) (hInv : ∀ x, w x * v x = 1)
    (μ : PositiveCylinderProbabilities) :
    continuousSquareReweight v hv (continuousSquareReweight w hw μ) = μ := by
  let ν := continuousSquareReweight w hw μ
  let A : ℝ := ‖continuousDensityVector μ w‖⁻¹
  let B : ℝ := ‖continuousDensityVector ν v‖⁻¹
  let c : ℝ := A ^ 2 * B ^ 2
  have hgw : Measurable (fun x => ENNReal.ofReal ((A * w x) ^ 2)) :=
    (measurable_const.mul w.continuous.measurable).pow_const 2 |>.ennreal_ofReal
  have hgv : Measurable (fun x => ENNReal.ofReal ((B * v x) ^ 2)) :=
    (measurable_const.mul v.continuous.measurable).pow_const 2 |>.ennreal_ofReal
  have hMeasure : ((continuousSquareReweight v hv ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      ENNReal.ofReal c • ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
    rw [continuousSquareReweight_measure v hv ν]
    have hν := congrArg (fun ρ : Measure HaarCantor =>
      ρ.withDensity (fun x => ENNReal.ofReal ((B * v x) ^ 2)))
        (continuousSquareReweight_measure w hw μ)
    change (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
      (fun x => ENNReal.ofReal ((B * v x) ^ 2))) = _
    refine hν.trans ?_
    change ((((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
      (fun x => ENNReal.ofReal ((A * w x) ^ 2))).withDensity
      (fun x => ENNReal.ofReal ((B * v x) ^ 2))) = _
    rw [← withDensity_mul _ hgw hgv]
    have heq : (fun x => ENNReal.ofReal ((A * w x) ^ 2)) *
        (fun x => ENNReal.ofReal ((B * v x) ^ 2)) = fun _ => ENNReal.ofReal c := by
      funext x
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      calc
        (A * w x) ^ 2 * (B * v x) ^ 2 = (A ^ 2 * B ^ 2) * (w x * v x) ^ 2 := by ring
        _ = c := by rw [hInv x]; simp only [one_pow, mul_one]; rfl
    rw [heq, withDensity_const]
  have hc : ENNReal.ofReal c = 1 := by
    have hm := congrArg (fun ρ : Measure HaarCantor => ρ univ) hMeasure
    simpa using hm.symm
  rw [hc, one_smul] at hMeasure
  apply Subtype.ext
  exact ProbabilityMeasure.toMeasure_injective hMeasure

def reciprocalContinuousMap (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) : C(HaarCantor, ℝ) :=
  ⟨fun x => (w x)⁻¹, w.continuous.inv₀ fun x => (hw x).ne'⟩

theorem reciprocalContinuousMap_positive (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    ∀ x, 0 < reciprocalContinuousMap w hw x := fun x => inv_pos.mpr (hw x)

def continuousSquareReweightHomeomorph (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    PositiveCylinderProbabilities ≃ₜ PositiveCylinderProbabilities :=
  { toEquiv :=
      { toFun := continuousSquareReweight w hw
        invFun := continuousSquareReweight (reciprocalContinuousMap w hw)
          (reciprocalContinuousMap_positive w hw)
        left_inv := continuousSquareReweight_inverse w (reciprocalContinuousMap w hw) hw
          (reciprocalContinuousMap_positive w hw) (fun x => mul_inv_cancel₀ (hw x).ne')
        right_inv := continuousSquareReweight_inverse (reciprocalContinuousMap w hw) w
          (reciprocalContinuousMap_positive w hw) hw (fun x => inv_mul_cancel₀ (hw x).ne') }
    continuous_toFun := continuous_continuousSquareReweight w hw
    continuous_invFun := continuous_continuousSquareReweight _ _ }

#print axioms continuousSquareReweightHomeomorph

end BenchmarkJump
