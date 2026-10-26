import CantorHaarCoordinates
import WeakIntegralContinuity
import Mathlib.Topology.CompactOpen

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def haarLipschitzIntegral (φ : ℝ → ℝ) {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (hφ0 : φ 0 = 0) (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) : ℝ :=
  inner ℝ (cantorOneVector μ) (hφ.compLp hφ0 (haarLift μ a))

theorem haarLipschitzIntegral_eq_integral (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0)
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    haarLipschitzIntegral φ hφ hφ0 μ a =
      ∫ x, φ (haarLift μ a x) ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [haarLipschitzIntegral, cantorOneVector, L2.inner_indicatorConstLp_one, setIntegral_univ]
  exact integral_congr_ae (hφ.coeFn_compLp hφ0 (haarLift μ a))

/-- A probability-uniform Lipschitz bound in the fixed coefficient space. -/
theorem haarLipschitzIntegral_dist_le (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0)
    (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (haarLipschitzIntegral φ hφ hφ0 μ a) (haarLipschitzIntegral φ hφ hφ0 μ b) ≤
      (K : ℝ) * dist a b := by
  rw [haarLipschitzIntegral, haarLipschitzIntegral, dist_eq_norm, ← inner_sub_right]
  calc
    _ ≤ ‖hφ.compLp hφ0 (haarLift μ a) - hφ.compLp hφ0 (haarLift μ b)‖ := by
      simpa only [cantorOneVector_norm, one_mul] using norm_inner_le_norm (cantorOneVector μ)
        (hφ.compLp hφ0 (haarLift μ a) - hφ.compLp hφ0 (haarLift μ b))
    _ ≤ (K : ℝ) * ‖haarLift μ a - haarLift μ b‖ :=
      hφ.norm_compLp_sub_le hφ0 (haarLift μ a) (haarLift μ b)
    _ = (K : ℝ) * dist a b := by rw [← dist_eq_norm, dist_haarLift]

theorem continuous_finiteHaar_integral (φ : ℝ → ℝ) (hφ : Continuous φ)
    (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      ∫ x, φ (finiteHaarFunction s p.1 p.2 x)
        ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) := by
  let F : (PositiveCylinderProbabilities × HaarCoefficientSpace) → C(HaarCantor, ℝ) := fun p =>
    ⟨fun x => φ (finiteHaarFunction s p.1 p.2 x),
      (hφ.comp (continuous_finiteHaarFunction s)).comp (continuous_const.prodMk continuous_id)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    (hφ.comp (continuous_finiteHaarFunction s))
  exact BenchmarkIntegration.continuous_probability_integral.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hF)

#print axioms haarLipschitzIntegral_dist_le
#print axioms continuous_finiteHaar_integral

end BenchmarkJump
