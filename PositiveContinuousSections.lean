import DensityBundleTopology
import HaarUnitCoordinateContinuity
import WeakIntegralContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def continuousDensityVector (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  ContinuousMap.toLp 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ℝ w

theorem continuousDensityVector_coe (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    continuousDensityVector μ w =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)] w :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ _

theorem continuousDensityVector_norm_sq (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    ‖continuousDensityVector μ w‖ ^ 2 =
      ∫ x, w x ^ 2 ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousDensityVector_coe μ w] with x hx
  rw [hx]
  simp [pow_two]

theorem continuous_continuousDensityVector_norm (w : C(HaarCantor, ℝ)) :
    Continuous (fun μ : PositiveCylinderProbabilities => ‖continuousDensityVector μ w‖) := by
  have hc := (ProbabilityMeasure.continuous_integral_continuousMap (w * w)).comp
    (continuous_subtype_val : Continuous (fun μ : PositiveCylinderProbabilities =>
      (μ : ProbabilityMeasure HaarCantor)))
  have heq : (fun μ : PositiveCylinderProbabilities =>
      Real.sqrt (∫ x, (w * w) x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))) =
      (fun μ : PositiveCylinderProbabilities => ‖continuousDensityVector μ w‖) := by
    funext μ
    have h := continuousDensityVector_norm_sq μ w
    have hint : (∫ x, (w * w) x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) =
        ‖continuousDensityVector μ w‖ ^ 2 := by
      simpa only [ContinuousMap.mul_apply, pow_two] using h.symm
    rw [hint, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact heq ▸ hc.sqrt

theorem continuousDensityVector_norm_pos (μ : PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x) : 0 < ‖continuousDensityVector μ w‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hzero : continuousDensityVector μ w =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      fun _ => (0 : ℝ) := by
    rw [hz]
    exact Lp.coeFn_zero _ _ _
  have hf : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor), False := by
    filter_upwards [continuousDensityVector_coe μ w, hzero] with x hx hz
    have hp := hpos x
    rw [← hx, hz] at hp
    exact lt_irrefl _ hp
  obtain ⟨_x, hx⟩ := hf.exists
  exact hx

def normalizedContinuousVector (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  ‖continuousDensityVector μ w‖⁻¹ • continuousDensityVector μ w

theorem normalizedContinuousVector_norm (μ : PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x) : ‖normalizedContinuousVector μ w‖ = 1 := by
  have hn := continuousDensityVector_norm_pos μ w hpos
  rw [normalizedContinuousVector, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

def continuousSectionCoefficients (w : C(HaarCantor, ℝ)) (μ : PositiveCylinderProbabilities) :
    HaarCoefficientSpace := (cantorRealHaarBasis μ).repr (normalizedContinuousVector μ w)

theorem continuousSectionCoefficients_norm (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) : ‖continuousSectionCoefficients w μ‖ = 1 := by
  rw [continuousSectionCoefficients, LinearIsometryEquiv.norm_map,
    normalizedContinuousVector_norm μ w hpos]

theorem continuous_haar_inner_fixed (w : C(HaarCantor, ℝ)) (i : Option HaarNodeIndex) :
    Continuous (fun μ : PositiveCylinderProbabilities =>
      inner ℝ (cantorHaarFamily μ i) (continuousDensityVector μ w)) := by
  let F : PositiveCylinderProbabilities → C(HaarCantor, ℝ) := fun μ =>
    ⟨fun x => haarFamilyFunction μ i x * w x,
      ((continuous_haarFamilyFunction i).comp (continuous_const.prodMk continuous_id)).mul w.continuous⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    ((continuous_haarFamilyFunction i).mul (w.continuous.comp continuous_snd))
  have hc := BenchmarkIntegration.continuous_probability_integral.comp
    (continuous_subtype_val.prodMk hF)
  have heq : (fun μ : PositiveCylinderProbabilities =>
      ∫ x, F μ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) =
      (fun μ : PositiveCylinderProbabilities =>
        inner ℝ (cantorHaarFamily μ i) (continuousDensityVector μ w)) := by
    funext μ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [haarFamilyFunction_coe μ i, continuousDensityVector_coe μ w] with x hx hy
    rw [hx, hy]
    simp only [F, Real.inner_apply]
    rfl
  change Continuous (fun μ : PositiveCylinderProbabilities =>
    ∫ x, F μ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) at hc
  rwa [heq] at hc

/-- Normalized positive continuous functions give genuine continuous
sections of the weak×Hilbert-coefficient density bundle. -/
theorem continuous_continuousSectionCoefficients (w : C(HaarCantor, ℝ))
    (hpos : ∀ x, 0 < w x) : Continuous (continuousSectionCoefficients w) := by
  apply continuous_haarCoefficients_of_unit_coordinates _ (continuousSectionCoefficients_norm w hpos)
  intro i
  have hformula : (fun μ : PositiveCylinderProbabilities => continuousSectionCoefficients w μ i) =
      (fun μ : PositiveCylinderProbabilities => ‖continuousDensityVector μ w‖⁻¹ *
        inner ℝ (cantorHaarFamily μ i) (continuousDensityVector μ w)) := by
    funext μ
    rw [continuousSectionCoefficients, HilbertBasis.repr_apply_apply, normalizedContinuousVector,
      real_inner_smul_right, cantorRealHaarBasis_apply]
  rw [hformula]
  exact ((continuous_continuousDensityVector_norm w).inv₀
    (fun μ => (continuousDensityVector_norm_pos μ w hpos).ne')).mul
      (continuous_haar_inner_fixed w i)

def positiveContinuousSection (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) : PositiveDensityBundle :=
  ⟨(μ, continuousSectionCoefficients w μ), by
    constructor
    · have hlift : haarLift μ (continuousSectionCoefficients w μ) = normalizedContinuousVector μ w :=
        (cantorRealHaarBasis μ).repr.symm_apply_apply _
      change ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
        0 < haarLift μ (continuousSectionCoefficients w μ) x
      rw [hlift]
      filter_upwards [Lp.coeFn_smul ‖continuousDensityVector μ w‖⁻¹ (continuousDensityVector μ w),
        continuousDensityVector_coe μ w] with x hx hy
      change 0 < (‖continuousDensityVector μ w‖⁻¹ • continuousDensityVector μ w) x
      simp only [Pi.smul_apply, smul_eq_mul] at hx
      rw [hx, hy]
      exact mul_pos (inv_pos.mpr (continuousDensityVector_norm_pos μ w hpos)) (hpos x)
    · exact continuousSectionCoefficients_norm w hpos μ⟩

theorem continuous_positiveContinuousSection (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x) :
    Continuous (positiveContinuousSection w hpos) :=
  (continuous_id.prodMk (continuous_continuousSectionCoefficients w hpos)).subtype_mk _

@[simp] theorem densitySource_positiveContinuousSection (w : C(HaarCantor, ℝ))
    (hpos : ∀ x, 0 < w x) (μ : PositiveCylinderProbabilities) :
    densitySource (positiveContinuousSection w hpos μ) = μ := rfl

#print axioms continuous_positiveContinuousSection

end BenchmarkJump
