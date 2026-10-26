import HaarLipschitzIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

private theorem lip_lp_finset_sum_coe {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (u : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, u i : Lp ℝ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (μ := μ) (E := ℝ) (p := 2))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with x hx hsum
      simpa only [Pi.add_apply, Finset.sum_insert ha] using
        hx.trans (congrArg (fun v => u a x + v) hsum)

theorem haarLift_trunc_eq_partial_sum (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    haarLift μ (haarCoefficientTrunc s a) = ∑ i ∈ s, a i • cantorHaarFamily μ i := by
  apply (cantorRealHaarBasis μ).repr.injective
  rw [haarLift, LinearIsometryEquiv.apply_symm_apply, repr_haar_partial_sum]

theorem haarLift_trunc_coe (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    haarLift μ (haarCoefficientTrunc s a) =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      finiteHaarFunction s μ a := by
  rw [haarLift_trunc_eq_partial_sum]
  have hOne (i : Option HaarNodeIndex) :
      (a i • cantorHaarFamily μ i) =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
        fun x => a i * haarFamilyFunction μ i x := by
    filter_upwards [Lp.coeFn_smul (a i) (cantorHaarFamily μ i), haarFamilyFunction_coe μ i]
      with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul] using hx.trans (congrArg (fun v => a i * v) hy)
  have hAll := eventually_countable_forall.mpr hOne
  filter_upwards [lip_lp_finset_sum_coe
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) s
      (fun i => a i • cantorHaarFamily μ i), hAll] with x hx hAllx
  rw [hx]
  simp_rw [hAllx]
  rfl

theorem haarLipschitzIntegral_trunc_eq (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0) (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    haarLipschitzIntegral φ hφ hφ0 μ (haarCoefficientTrunc s a) =
      ∫ x, φ (finiteHaarFunction s μ a x)
        ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [haarLipschitzIntegral_eq_integral]
  exact integral_congr_ae ((haarLift_trunc_coe μ s a).fun_comp φ)

theorem continuous_haarLipschitzIntegral_trunc (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0) (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 (haarCoefficientTrunc s p.2)) := by
  have heq : (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 (haarCoefficientTrunc s p.2)) =
      (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
        ∫ x, φ (finiteHaarFunction s p.1 p.2 x)
          ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
    funext fun p => haarLipschitzIntegral_trunc_eq φ hφ hφ0 p.1 s p.2
  rw [heq]
  exact continuous_finiteHaar_integral φ hφ.continuous s

/-- Actual varying-measure Lipschitz integrals are jointly continuous in
the weak probability parameter and normed Haar coefficients. -/
theorem continuous_haarLipschitzIntegral (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := (K : ℝ) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : (K : ℝ) ≤ L := by dsimp [L]; linarith
  let δ : ℝ := ε / (8 * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc p₀.2) δ hδ).exists
  let b := haarCoefficientTrunc s p₀.2
  have hb : dist b p₀.2 < δ := hs
  have hFixed : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 b) :=
    (continuous_haarLipschitzIntegral_trunc φ hφ hφ0 s).comp
      (continuous_fst.prodMk (continuous_const (y := p₀.2)))
  have hNearF := Metric.tendsto_nhds.mp (hFixed.tendsto p₀) (ε / 2) (by positivity)
  have hNearA := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace => p.2)).tendsto p₀)
      δ hδ
  filter_upwards [hNearF, hNearA] with p hpF hpA
  have hTri := dist_triangle
    (haarLipschitzIntegral φ hφ hφ0 p.1 p.2)
    (haarLipschitzIntegral φ hφ hφ0 p.1 b)
    (haarLipschitzIntegral φ hφ hφ0 p₀.1 p₀.2)
  have hTri2 := dist_triangle
    (haarLipschitzIntegral φ hφ hφ0 p.1 b)
    (haarLipschitzIntegral φ hφ hφ0 p₀.1 b)
    (haarLipschitzIntegral φ hφ hφ0 p₀.1 p₀.2)
  have hA := haarLipschitzIntegral_dist_le φ hφ hφ0 p.1 p.2 b
  have hB := haarLipschitzIntegral_dist_le φ hφ hφ0 p₀.1 b p₀.2
  have hAB : dist p.2 b ≤ dist p.2 p₀.2 + dist b p₀.2 := by
    simpa only [dist_comm b p₀.2] using dist_triangle p.2 p₀.2 b
  have hA' : (K : ℝ) * dist p.2 b ≤ L * (dist p.2 p₀.2 + dist b p₀.2) :=
    mul_le_mul hKL hAB dist_nonneg hL.le
  have hB' : (K : ℝ) * dist b p₀.2 ≤ L * dist b p₀.2 :=
    mul_le_mul_of_nonneg_right hKL dist_nonneg
  have hCalc : L * δ = ε / 8 := by
    dsimp [δ]
    field_simp
  nlinarith

#print axioms continuous_haarLipschitzIntegral

end BenchmarkJump
