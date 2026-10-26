import PositiveContinuousSections
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem normalize_dist_le_twice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g f : E) (hg : g ≠ 0) (hf : ‖f‖ = 1) :
    dist (‖g‖⁻¹ • g) f ≤ 2 * dist g f := by
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hscale : dist (‖g‖⁻¹ • g) g = |1 - ‖g‖| := by
    rw [dist_eq_norm]
    have heq : ‖g‖⁻¹ • g - g = (‖g‖⁻¹ - 1) • g := by module
    rw [heq, norm_smul, Real.norm_eq_abs]
    calc
      |‖g‖⁻¹ - 1| * ‖g‖ = |(‖g‖⁻¹ - 1) * ‖g‖| := by
        rw [abs_mul, abs_of_pos hn]
      _ = |1 - ‖g‖| := by congr 1; field_simp
  have hrev : |1 - ‖g‖| ≤ dist g f := by
    simpa only [hf, abs_sub_comm, dist_eq_norm] using abs_norm_sub_norm_le g f
  have ht := dist_triangle (‖g‖⁻¹ • g) g f
  rw [hscale] at ht
  linarith

/-- Strictly-positive continuous functions, normalized in L2, are dense
among positive unit densities for the genuine Cantor measure. -/
theorem positive_continuous_vectors_dense (μ : PositiveCylinderProbabilities)
    (f : Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hPos : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor), 0 < f x)
    (hNorm : ‖f‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : C(HaarCantor, ℝ), (∀ x, 0 < w x) ∧ dist (normalizedContinuousVector μ w) f < ε := by
  let ν : Measure HaarCantor := ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  let η : ℝ := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  have hd : DenseRange (ContinuousMap.toLp 2 ν ℝ : C(HaarCantor, ℝ) →L[ℝ] Lp ℝ 2 ν) :=
    ContinuousMap.toLp_denseRange _ _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨v, hv⟩ := hd.exists_dist_lt f hη
  let ψ : ℝ → ℝ := fun t => max t 0
  have hψ : LipschitzWith 1 ψ := LipschitzWith.id.max_const 0
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  let w : C(HaarCantor, ℝ) :=
    ⟨fun x => max (v x) 0 + η, (v.continuous.max continuous_const).add continuous_const⟩
  have hwPos : ∀ x, 0 < w x := by
    intro x
    exact add_pos_of_nonneg_of_pos (le_max_right _ _) hη
  have hFix : hψ.compLp hψ0 f = f := by
    apply Lp.ext
    filter_upwards [hψ.coeFn_compLp hψ0 f, hPos] with x hx hp
    simpa only [ψ, Function.comp_apply, max_eq_left hp.le] using hx
  have hwEq : continuousDensityVector μ w =
      hψ.compLp hψ0 (continuousDensityVector μ v) + η • cantorOneVector μ := by
    apply Lp.ext
    filter_upwards [continuousDensityVector_coe μ w,
      Lp.coeFn_add (hψ.compLp hψ0 (continuousDensityVector μ v)) (η • cantorOneVector μ),
      hψ.coeFn_compLp hψ0 (continuousDensityVector μ v),
      Lp.coeFn_smul η (cantorOneVector μ), haarFamilyFunction_coe μ none,
      continuousDensityVector_coe μ v] with x hw ha hc hs h1 hv
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at ha hc hs
    change cantorOneVector μ x = 1 at h1
    rw [hw, ha, hc, hs, h1, hv]
    simp only [w, ψ, mul_one]
    rfl
  have hComp : ‖hψ.compLp hψ0 (continuousDensityVector μ v) - f‖ ≤
      ‖continuousDensityVector μ v - f‖ := by
    have h := hψ.norm_compLp_sub_le hψ0 (continuousDensityVector μ v) f
    simpa only [hFix, NNReal.coe_one, one_mul] using h
  have hOne : ‖η • cantorOneVector μ‖ = η := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, cantorOneVector_norm, mul_one]
  have hErr : dist (continuousDensityVector μ w) f < 2 * η := by
    rw [dist_eq_norm, hwEq]
    have heq : hψ.compLp hψ0 (continuousDensityVector μ v) + η • cantorOneVector μ - f =
        (hψ.compLp hψ0 (continuousDensityVector μ v) - f) + η • cantorOneVector μ := by module
    rw [heq]
    have ht := norm_add_le (hψ.compLp hψ0 (continuousDensityVector μ v) - f) (η • cantorOneVector μ)
    rw [hOne] at ht
    rw [dist_comm] at hv
    change dist (continuousDensityVector μ v) f < η at hv
    rw [dist_eq_norm] at hv
    linarith
  have hn := continuousDensityVector_norm_pos μ w hwPos
  refine ⟨w, hwPos, ?_⟩
  have hBound := normalize_dist_le_twice (continuousDensityVector μ w) f
    (norm_pos_iff.mp hn) hNorm
  change dist (‖continuousDensityVector μ w‖⁻¹ • continuousDensityVector μ w) f < ε
  dsimp [η] at hErr
  linarith

/-- At any bundle point, values of the proved continuous positive sections
are norm dense in its source fiber. -/
theorem positiveContinuousSection_fiber_dense (z : PositiveDensityBundle)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : C(HaarCantor, ℝ), ∃ hpos : ∀ x, 0 < w x,
      dist (continuousSectionCoefficients w (densitySource z)) z.1.2 < ε := by
  obtain ⟨w, hw, hNear⟩ := positive_continuous_vectors_dense (densitySource z)
    (densityVector z) (densityVector_positive z) (densityVector_norm z) ε hε
  refine ⟨w, hw, ?_⟩
  have hrepr : (cantorRealHaarBasis (densitySource z)).repr (densityVector z) = z.1.2 :=
    (cantorRealHaarBasis (densitySource z)).repr.apply_symm_apply _
  have hdist := (cantorRealHaarBasis (densitySource z)).repr.isometry.dist_eq
    (normalizedContinuousVector (densitySource z) w) (densityVector z)
  change dist ((cantorRealHaarBasis (densitySource z)).repr
    (normalizedContinuousVector (densitySource z) w)) z.1.2 < ε
  rw [← hrepr, hdist]
  exact hNear

#print axioms positiveContinuousSection_fiber_dense

end BenchmarkJump
