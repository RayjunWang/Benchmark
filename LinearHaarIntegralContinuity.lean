import PositiveContinuousSections
import HaarIntegralContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

theorem continuousDensityVector_norm_le (μ : PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) : ‖continuousDensityVector μ w‖ ≤ ‖w‖ := by
  have hOp : ‖(ContinuousMap.toLp 2
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ℝ :
      C(HaarCantor, ℝ) →L[ℝ] Lp ℝ 2
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))‖ ≤ 1 := by
    simpa [measureUnivNNReal] using ContinuousMap.toLp_norm_le (p := (2 : ℝ≥0∞))
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (𝕜 := ℝ) (E := ℝ)
  exact (ContinuousLinearMap.le_opNorm _ w).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hOp (norm_nonneg w))

def linearHaarIntegral (w : C(HaarCantor, ℝ)) (μ : PositiveCylinderProbabilities)
    (a : HaarCoefficientSpace) : ℝ := inner ℝ (continuousDensityVector μ w) (haarLift μ a)

theorem linearHaarIntegral_eq_integral (w : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    linearHaarIntegral w μ a =
      ∫ x, w x * haarLift μ a x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [linearHaarIntegral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousDensityVector_coe μ w] with x hx
  rw [hx, Real.inner_apply, mul_comm]

theorem linearHaarIntegral_coefficient_dist_le (w : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (linearHaarIntegral w μ a) (linearHaarIntegral w μ b) ≤ ‖w‖ * dist a b := by
  rw [linearHaarIntegral, linearHaarIntegral, dist_eq_norm, ← inner_sub_right]
  calc
    _ ≤ ‖continuousDensityVector μ w‖ * ‖haarLift μ a - haarLift μ b‖ :=
      norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ ‖w‖ * ‖haarLift μ a - haarLift μ b‖ :=
      mul_le_mul_of_nonneg_right (continuousDensityVector_norm_le μ w) (norm_nonneg _)
    _ = _ := by rw [← dist_eq_norm, dist_haarLift]

theorem linearHaarIntegral_test_dist_le (w v : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    dist (linearHaarIntegral w μ a) (linearHaarIntegral v μ a) ≤ dist w v * ‖a‖ := by
  rw [linearHaarIntegral, linearHaarIntegral, dist_eq_norm, ← inner_sub_left]
  have hSub : continuousDensityVector μ w - continuousDensityVector μ v =
      continuousDensityVector μ (w - v) := (map_sub _ w v).symm
  rw [hSub]
  calc
    _ ≤ ‖continuousDensityVector μ (w - v)‖ * ‖haarLift μ a‖ :=
      norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ ‖w - v‖ * ‖haarLift μ a‖ :=
      mul_le_mul_of_nonneg_right (continuousDensityVector_norm_le μ (w - v)) (norm_nonneg _)
    _ = _ := by rw [dist_eq_norm, norm_haarLift]

theorem linearHaarIntegral_trunc_eq (w : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (s : Finset (Option HaarNodeIndex))
    (a : HaarCoefficientSpace) :
    linearHaarIntegral w μ (haarCoefficientTrunc s a) =
      ∫ x, w x * finiteHaarFunction s μ a x
        ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [linearHaarIntegral_eq_integral]
  apply integral_congr_ae
  filter_upwards [haarLift_trunc_coe μ s a] with x hx
  rw [hx]

theorem continuous_linearHaarIntegral_trunc (w : C(HaarCantor, ℝ))
    (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      linearHaarIntegral w p.1 (haarCoefficientTrunc s p.2)) := by
  let F : (PositiveCylinderProbabilities × HaarCoefficientSpace) → C(HaarCantor, ℝ) := fun p =>
    ⟨fun x => w x * finiteHaarFunction s p.1 p.2 x,
      w.continuous.mul ((continuous_finiteHaarFunction s).comp
        (continuous_const.prodMk continuous_id))⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    ((w.continuous.comp continuous_snd).mul (continuous_finiteHaarFunction s))
  have hc := BenchmarkIntegration.continuous_probability_integral.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hF)
  change Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
    ∫ x, w x * finiteHaarFunction s p.1 p.2 x
      ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) at hc
  simpa only [linearHaarIntegral_trunc_eq] using hc

theorem continuous_linearHaarIntegral (w : C(HaarCantor, ℝ)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      linearHaarIntegral w p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := ‖w‖ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hwL : ‖w‖ ≤ L := by dsimp [L]; linarith
  let δ : ℝ := ε / (8 * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc p₀.2) δ hδ).exists
  let b := haarCoefficientTrunc s p₀.2
  have hb : dist b p₀.2 < δ := hs
  have hFixed : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      linearHaarIntegral w p.1 b) :=
    (continuous_linearHaarIntegral_trunc w s).comp
      (continuous_fst.prodMk (continuous_const (y := p₀.2)))
  have hNearF := Metric.tendsto_nhds.mp (hFixed.tendsto p₀) (ε / 2) (by positivity)
  have hNearA := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace => p.2)).tendsto p₀)
      δ hδ
  filter_upwards [hNearF, hNearA] with p hpF hpA
  have hTri := dist_triangle (linearHaarIntegral w p.1 p.2)
    (linearHaarIntegral w p.1 b) (linearHaarIntegral w p₀.1 p₀.2)
  have hTri2 := dist_triangle (linearHaarIntegral w p.1 b)
    (linearHaarIntegral w p₀.1 b) (linearHaarIntegral w p₀.1 p₀.2)
  have hA := linearHaarIntegral_coefficient_dist_le w p.1 p.2 b
  have hB := linearHaarIntegral_coefficient_dist_le w p₀.1 b p₀.2
  have hAB : dist p.2 b ≤ dist p.2 p₀.2 + dist b p₀.2 := by
    simpa only [dist_comm b p₀.2] using dist_triangle p.2 p₀.2 b
  have hA' : ‖w‖ * dist p.2 b ≤ L * (dist p.2 p₀.2 + dist b p₀.2) :=
    mul_le_mul hwL hAB dist_nonneg hL.le
  have hB' : ‖w‖ * dist b p₀.2 ≤ L * dist b p₀.2 :=
    mul_le_mul_of_nonneg_right hwL dist_nonneg
  have hCalc : L * δ = ε / 8 := by dsimp [δ]; field_simp
  nlinarith

theorem continuous_linearHaarIntegral_joint :
    Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) × C(HaarCantor, ℝ) =>
      linearHaarIntegral p.2 p.1.1 p.1.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := ‖p₀.1.2‖ + 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hA := Metric.tendsto_nhds.mp
    ((continuous_snd.comp continuous_fst :
      Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) ×
        C(HaarCantor, ℝ) => p.1.2)).tendsto p₀) 1 (by norm_num)
  have hW := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) ×
      C(HaarCantor, ℝ) => p.2)).tendsto p₀) (ε / (2 * L)) (by positivity)
  have hF := Metric.tendsto_nhds.mp
    (((continuous_linearHaarIntegral p₀.2).comp continuous_fst).tendsto p₀)
      (ε / 2) (by positivity)
  filter_upwards [hA, hW, hF] with p hpA hpW hpF
  change dist p.1.2 p₀.1.2 < 1 at hpA
  change dist (linearHaarIntegral p₀.2 p.1.1 p.1.2)
    (linearHaarIntegral p₀.2 p₀.1.1 p₀.1.2) < ε / 2 at hpF
  have hN : ‖p.1.2‖ ≤ L := by
    have hn : ‖p.1.2‖ ≤ dist p.1.2 p₀.1.2 + ‖p₀.1.2‖ := by
      simpa only [dist_zero_right] using dist_triangle p.1.2 p₀.1.2 0
    dsimp [L]
    linarith
  have hB := linearHaarIntegral_test_dist_le p.2 p₀.2 p.1.1 p.1.2
  have hB' : dist p.2 p₀.2 * ‖p.1.2‖ ≤ dist p.2 p₀.2 * L :=
    mul_le_mul_of_nonneg_left hN dist_nonneg
  have hSmall := mul_lt_mul_of_pos_right hpW hL
  have he : ε / (2 * L) * L = ε / 2 := by field_simp
  have hTri := dist_triangle (linearHaarIntegral p.2 p.1.1 p.1.2)
    (linearHaarIntegral p₀.2 p.1.1 p.1.2) (linearHaarIntegral p₀.2 p₀.1.1 p₀.1.2)
  linarith

#print axioms continuous_linearHaarIntegral_joint

end BenchmarkJump
