import BernoulliSpectralGap

/-! A concrete measured expansion estimate for the two-generator Bernoulli shift. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace symmDiff

noncomputable section

namespace BenchmarkShift

def constantL2 (c : ℝ) : BernoulliL2 := Lp.const 2 bernoulli c

lemma constantL2_ae (c : ℝ) : (constantL2 c : Point → ℝ) =ᵐ[bernoulli] fun _ => c :=
  Lp.coeFn_const _ _ _

lemma norm_constantL2 (c : ℝ) : ‖constantL2 c‖ = |c| := by
  simp [constantL2, Lp.norm_const' 2 bernoulli c (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

lemma inner_constantL2_one (u : BernoulliL2) :
    ⟪constantL2 1, u⟫_ℝ = ∫ x, u x ∂bernoulli := by
  rw [constantL2, ← indicatorConstLp_univ]
  simpa using L2.inner_indicatorConstLp_one MeasurableSet.univ
    (measure_ne_top bernoulli univ) u

lemma constantL2_smul (c : ℝ) : constantL2 c = c • constantL2 1 := by
  apply Lp.ext
  filter_upwards [constantL2_ae c, constantL2_ae 1,
    Lp.coeFn_smul c (constantL2 1)] with x hx hy hz
  simp only [hx, hz, Pi.smul_apply, smul_eq_mul, hy, mul_one]

lemma koopman_constantL2 (g : Group) (c : ℝ) : koopman g (constantL2 c) = constantL2 c := by
  apply Lp.ext
  filter_upwards [koopman_ae g (constantL2 c), constantL2_ae c,
    (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae (constantL2_ae c)] with x hx hy hz
  exact hx.trans (hz.trans hy.symm)

theorem bernoulli_variance_gap (u : BernoulliL2) :
    ‖u‖ ^ 2 - (∫ x, u x ∂bernoulli) ^ 2 ≤ 8 *
      (‖koopman (letterGroup (0, true)) u - u‖ ^ 2 +
        ‖koopman (letterGroup (1, true)) u - u‖ ^ 2) := by
  let m := ∫ x, u x ∂bernoulli
  let v := u - constantL2 m
  have hinner : ⟪constantL2 1, v⟫_ℝ = 0 := by
    dsimp only [v]
    rw [inner_sub_right, constantL2_smul m, inner_smul_right]
    rw [inner_self_eq_norm_sq_to_K, norm_constantL2, inner_constantL2_one]
    norm_num [m]
  have hmean : (∫ x, v x ∂bernoulli) = 0 := by
    rw [← inner_constantL2_one]
    exact hinner
  have hnorm : ‖v‖ ^ 2 = ‖u‖ ^ 2 - m ^ 2 := by
    dsimp only [v]
    rw [norm_sub_sq_real, norm_constantL2, constantL2_smul m,
      inner_smul_right, real_inner_comm, inner_constantL2_one]
    rw [sq_abs]
    ring
  have hdiff (g : Group) : koopman g v - v = koopman g u - u := by
    dsimp only [v]
    rw [map_sub, koopman_constantL2]
    abel
  have hgap := bernoulli_L2_spectral_gap v hmean
  rwa [hnorm, hdiff, hdiff] at hgap

def indicatorL2 (s : Set Point) (hs : MeasurableSet s) : BernoulliL2 :=
  indicatorConstLp 2 hs (measure_ne_top bernoulli s) (1 : ℝ)

lemma norm_sq_indicatorL2 (s : Set Point) (hs : MeasurableSet s) :
    ‖indicatorL2 s hs‖ ^ 2 = bernoulli.real s := by
  rw [← real_inner_self_eq_norm_sq]
  simpa [indicatorL2] using L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hs hs

lemma integral_indicatorL2 (s : Set Point) (hs : MeasurableSet s) :
    (∫ x, indicatorL2 s hs x ∂bernoulli) = bernoulli.real s := by
  rw [← inner_constantL2_one, constantL2, ← indicatorConstLp_univ]
  simpa [indicatorL2] using
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one MeasurableSet.univ hs
      (μ := bernoulli)

lemma koopman_indicatorL2 (g : Group) (s : Set Point) (hs : MeasurableSet s) :
    koopman g (indicatorL2 s hs) =
      indicatorL2 ((shift g⁻¹) ⁻¹' s) (hs.preimage (continuous_shift g⁻¹).measurable) := by
  apply Lp.ext
  have ht := (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
      (hμs := measure_ne_top bernoulli s) (c := (1 : ℝ)))
  filter_upwards [koopman_ae g (indicatorL2 s hs), ht,
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
      (hs := hs.preimage (continuous_shift g⁻¹).measurable)
      (hμs := measure_ne_top bernoulli _) (c := (1 : ℝ)))] with x hx hy hz
  exact hx.trans (hy.trans (by simpa only [Set.indicator_comp_right] using hz.symm))

lemma norm_sq_indicatorL2_sub (s t : Set Point) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ‖indicatorL2 s hs - indicatorL2 t ht‖ ^ 2 = bernoulli.real (s ∆ t) := by
  rw [← dist_eq_norm, indicatorL2, indicatorL2, dist_indicatorConstLp_eq_norm]
  exact norm_sq_indicatorL2 (s ∆ t) (hs.symmDiff ht)

theorem bernoulli_set_expansion (s : Set Point) (hs : MeasurableSet s)
    (hsmall : bernoulli.real s ≤ 1 / 2) :
    bernoulli.real s ≤ 16 *
      (bernoulli.real (((shift (letterGroup (0, true))⁻¹) ⁻¹' s) ∆ s) +
       bernoulli.real (((shift (letterGroup (1, true))⁻¹) ⁻¹' s) ∆ s)) := by
  have hgap := bernoulli_variance_gap (indicatorL2 s hs)
  rw [norm_sq_indicatorL2, integral_indicatorL2, koopman_indicatorL2,
    koopman_indicatorL2, norm_sq_indicatorL2_sub, norm_sq_indicatorL2_sub] at hgap
  have hnonneg : 0 ≤ bernoulli.real s := ENNReal.toReal_nonneg
  nlinarith

end BenchmarkShift

#print axioms BenchmarkShift.bernoulli_set_expansion
