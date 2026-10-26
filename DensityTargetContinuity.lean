import DensityBundleTopology
import SquareTestEstimate
import HaarIntegralContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def squareHaarIntegral (h : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) : ℝ :=
  ∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ a) : Measure HaarCantor)

theorem squareHaarIntegral_dist_le (h : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (squareHaarIntegral h μ a) (squareHaarIntegral h μ b) ≤
      ‖h‖ * dist a b * (‖a‖ + ‖b‖) := by
  have hBound := BenchmarkIntegration.square_test_difference_bound
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ a) (haarLift μ b) h
  simpa only [squareHaarIntegral, Real.dist_eq, ← dist_eq_norm,
    dist_haarLift, norm_haarLift] using hBound

theorem squareHaarIntegral_trunc_eq (h : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (s : Finset (Option HaarNodeIndex))
    (a : HaarCoefficientSpace) :
    squareHaarIntegral h μ (haarCoefficientTrunc s a) =
      ∫ x, h x * (finiteHaarFunction s μ a x) ^ 2
        ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [squareHaarIntegral, MeasureEquivalenceDensity.squareMeasure_integral]
  apply integral_congr_ae
  filter_upwards [haarLift_trunc_coe μ s a] with x hx
  rw [hx, mul_comm]

theorem continuous_squareHaarIntegral_trunc (h : C(HaarCantor, ℝ))
    (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      squareHaarIntegral h p.1 (haarCoefficientTrunc s p.2)) := by
  let F : (PositiveCylinderProbabilities × HaarCoefficientSpace) → C(HaarCantor, ℝ) := fun p =>
    ⟨fun x => h x * (finiteHaarFunction s p.1 p.2 x) ^ 2,
      h.continuous.mul (((continuous_finiteHaarFunction s).comp
        (continuous_const.prodMk continuous_id)).pow 2)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    ((h.continuous.comp continuous_snd).mul ((continuous_finiteHaarFunction s).pow 2))
  have hc := BenchmarkIntegration.continuous_probability_integral.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hF)
  change Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
    ∫ x, h x * (finiteHaarFunction s p.1 p.2 x) ^ 2
      ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) at hc
  simpa only [squareHaarIntegral_trunc_eq] using hc

/- Weak integrals of the actual square density vary continuously with both
the source probability and the common Hilbert coefficients. -/
set_option maxHeartbeats 500000 in
theorem continuous_squareHaarIntegral (h : C(HaarCantor, ℝ)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      squareHaarIntegral h p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := (‖h‖ + 1) * (2 * ‖p₀.2‖ + 3)
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := min 1 (ε / (8 * C))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδe : C * δ ≤ ε / 8 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (ε / (8 * C))) hC.le
    have he : C * (ε / (8 * C)) = ε / 8 := by field_simp
    exact hh.trans_eq he
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc p₀.2) δ hδ).exists
  let b := haarCoefficientTrunc s p₀.2
  have hb : dist b p₀.2 < δ := hs
  have hbN : ‖b‖ ≤ ‖p₀.2‖ + 1 := by
    have hn : ‖b‖ ≤ dist b p₀.2 + ‖p₀.2‖ := by
      simpa only [dist_zero_right] using dist_triangle b p₀.2 0
    linarith only [hn, hb, hδ1]
  have hFixed : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      squareHaarIntegral h p.1 b) := by
    have hPair : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
        (p.1, p₀.2)) := continuous_fst.prodMk continuous_const
    have hc := (continuous_squareHaarIntegral_trunc h s).comp hPair
    exact hc
  have hNearF := Metric.tendsto_nhds.mp (hFixed.tendsto p₀) (ε / 2) (by positivity)
  have hNearA := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace => p.2)).tendsto p₀)
      δ hδ
  filter_upwards [hNearF, hNearA] with p hpF hpA
  change dist (squareHaarIntegral h p.1 b) (squareHaarIntegral h p₀.1 b) < ε / 2 at hpF
  have hpN : ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
    have hn : ‖p.2‖ ≤ dist p.2 p₀.2 + ‖p₀.2‖ := by
      simpa only [dist_zero_right] using dist_triangle p.2 p₀.2 0
    linarith only [hn, hpA, hδ1]
  have hLocal (u v : HaarCoefficientSpace) (hu : ‖u‖ ≤ ‖p₀.2‖ + 1)
      (hv : ‖v‖ ≤ ‖p₀.2‖ + 1) (μ : PositiveCylinderProbabilities) :
      dist (squareHaarIntegral h μ u) (squareHaarIntegral h μ v) ≤ C * dist u v := by
    have hsN : ‖u‖ + ‖v‖ ≤ 2 * ‖p₀.2‖ + 3 := by linarith only [hu, hv]
    have hh : ‖h‖ * (‖u‖ + ‖v‖) ≤ C := by
      dsimp [C]
      exact mul_le_mul (by linarith only [norm_nonneg h]) hsN (by positivity) (by positivity)
    calc
      _ ≤ ‖h‖ * dist u v * (‖u‖ + ‖v‖) := squareHaarIntegral_dist_le h μ u v
      _ = (‖h‖ * (‖u‖ + ‖v‖)) * dist u v := by ring
      _ ≤ C * dist u v := mul_le_mul_of_nonneg_right hh dist_nonneg
  have hA := hLocal p.2 b hpN hbN p.1
  have hB := hLocal b p₀.2 hbN (by linarith only) p₀.1
  have hTri := dist_triangle (squareHaarIntegral h p.1 p.2)
    (squareHaarIntegral h p.1 b) (squareHaarIntegral h p₀.1 p₀.2)
  have hTri2 := dist_triangle (squareHaarIntegral h p.1 b)
    (squareHaarIntegral h p₀.1 b) (squareHaarIntegral h p₀.1 p₀.2)
  have hAB : dist p.2 b ≤ dist p.2 p₀.2 + dist b p₀.2 := by
    simpa only [dist_comm b p₀.2] using dist_triangle p.2 p₀.2 b
  have hMul := mul_le_mul_of_nonneg_left hAB hC.le
  rw [mul_add] at hMul
  have hSmallA := mul_lt_mul_of_pos_left hpA hC
  have hSmallB := mul_lt_mul_of_pos_left hb hC
  linarith only [hTri, hTri2, hA, hB, hMul, hSmallA, hSmallB, hδe, hpF, hε]

theorem continuous_densityTargetProbability : Continuous densityTargetProbability := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro h
  change Continuous (fun z : PositiveDensityBundle => squareHaarIntegral h z.1.1 z.1.2)
  exact (continuous_squareHaarIntegral h).comp continuous_subtype_val

theorem continuous_densityTarget : Continuous densityTarget :=
  continuous_densityTargetProbability.subtype_mk _

#print axioms continuous_densityTarget

end BenchmarkJump
