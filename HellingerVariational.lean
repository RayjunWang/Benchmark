import HellingerAffinity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Semicontinuity.Basic

/-! Continuous positive test functions for Hellinger affinity. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceHellinger

private theorem sqrt_product_le_test (p q f : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hf : 0 < f) : Real.sqrt p * Real.sqrt q ≤ (f * p + f⁻¹ * q) / 2 := by
  have hid : f * p + f⁻¹ * q - 2 * (Real.sqrt p * Real.sqrt q) =
      (f * Real.sqrt p - Real.sqrt q) ^ 2 / f := by
    rw [sub_sq, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
    field_simp
    ring
  have hnonneg := div_nonneg (sq_nonneg (f * Real.sqrt p - Real.sqrt q)) hf.le
  rw [← hid] at hnonneg
  linarith

private theorem abs_clip_sub_le (c C u v : ℝ) (hvc : c ≤ v) (hvC : v ≤ C) :
    |max c (min C u) - v| ≤ |u - v| := by
  by_cases huc : u ≤ c
  · have humin : min C u ≤ c := (min_le_right _ _).trans huc
    rw [max_eq_left humin, abs_of_nonpos (sub_nonpos.mpr hvc),
      abs_of_nonpos (sub_nonpos.mpr (huc.trans hvc))]
    linarith
  · by_cases huC : C ≤ u
    · rw [min_eq_left huC, max_eq_right (hvc.trans hvC),
        abs_of_nonneg (sub_nonneg.mpr hvC),
        abs_of_nonneg (sub_nonneg.mpr (hvC.trans huC))]
      linarith
    · rw [min_eq_right (le_of_not_ge huC), max_eq_right (le_of_not_ge huc)]

private theorem inverse_lipschitz_on_Ici (c u v : ℝ) (hc : 0 < c)
    (hu : c ≤ u) (hv : c ≤ v) :
    |u⁻¹ - v⁻¹| ≤ (c * c)⁻¹ * |u - v| := by
  have hu0 : 0 < u := hc.trans_le hu
  have hv0 : 0 < v := hc.trans_le hv
  rw [inv_sub_inv hu0.ne' hv0.ne', abs_div,
    abs_of_pos (mul_pos hu0 hv0), abs_sub_comm v u]
  have huv : c * c ≤ u * v := mul_le_mul hu hv hc.le hu0.le
  calc
    |u - v| / (u * v) ≤ |u - v| / (c * c) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc hc) huv
    _ = _ := by ring

/-- The positive-test functional in the Hellinger variational formula. -/
noncomputable def affinityTest {Z : Type*} [MeasurableSpace Z]
    (μ ν : Measure Z) (f : Z → ℝ) : ℝ :=
  ((∫ z, f z ∂μ) + ∫ z, (f z)⁻¹ ∂ν) / 2

/-- The easy half of the variational formula follows from pointwise
arithmetic--geometric mean, with the integrability requirements stated. -/
theorem affinity_le_affinityTest_of_integrable
    {Z : Type*} [MeasurableSpace Z]
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Z → ℝ) (hfpos : ∀ z, 0 < f z)
    (hfμ : Integrable f μ) (hfinvν : Integrable (fun z => (f z)⁻¹) ν) :
    affinity μ ν ≤ affinityTest μ ν f := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hiP := (integrable_toReal_rnDeriv_mul_iff hμ).mpr hfμ
  have hiQ := (integrable_toReal_rnDeriv_mul_iff hν).mpr hfinvν
  rw [affinity_integral]
  calc
    _ ≤ ∫ z, ((μ.rnDeriv (μ + ν) z).toReal * f z +
        (ν.rnDeriv (μ + ν) z).toReal * (f z)⁻¹) / 2 ∂(μ + ν) := by
      apply integral_mono (integrable_affinity_integrand μ ν) ((hiP.add hiQ).div_const 2)
      intro z
      simpa only [mul_comm] using sqrt_product_le_test
        (μ.rnDeriv (μ + ν) z).toReal (ν.rnDeriv (μ + ν) z).toReal (f z)
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hfpos z)
    _ = affinityTest μ ν f := by
      rw [integral_div, integral_add hiP hiQ,
        integral_toReal_rnDeriv_mul hμ, integral_toReal_rnDeriv_mul hν]
      rfl

private noncomputable def regularizer (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem regularizer_pos (n : ℕ) : 0 < regularizer n := by
  unfold regularizer
  positivity

private theorem regularizer_le_one (n : ℕ) : regularizer n ≤ 1 := by
  unfold regularizer
  apply (div_le_one (by positivity)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem regularizer_tendsto : Tendsto regularizer atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem weighted_ratio_le_two (p q d : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    p * ((Real.sqrt q + d) / (Real.sqrt p + d)) ≤ 2 := by
  have hden : 0 < Real.sqrt p + d := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hd
  have hpdiv : p / (Real.sqrt p + d) ≤ Real.sqrt p := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hsp : Real.sqrt p ≤ 1 := by nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hsq : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  calc
    _ = (p / (Real.sqrt p + d)) * (Real.sqrt q + d) := by ring
    _ ≤ Real.sqrt p * (Real.sqrt q + d) :=
      mul_le_mul_of_nonneg_right hpdiv (by positivity)
    _ ≤ 1 * 2 := mul_le_mul hsp (by linarith) (by positivity) (by norm_num)
    _ = 2 := by ring

private theorem weighted_ratio_tendsto (p q : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun n => p * ((Real.sqrt q + regularizer n) /
      (Real.sqrt p + regularizer n))) atTop (𝓝 (Real.sqrt p * Real.sqrt q)) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsp : Real.sqrt p ≠ 0 :=
    (Real.sqrt_pos.mpr (lt_of_le_of_ne hp (fun h => hp0 h.symm))).ne'
  have ht : Tendsto (fun n => p * ((Real.sqrt q + regularizer n) /
      (Real.sqrt p + regularizer n))) atTop
      (𝓝 (p * ((Real.sqrt q + 0) / (Real.sqrt p + 0)))) :=
    tendsto_const_nhds.mul
      ((tendsto_const_nhds.add regularizer_tendsto).div
        (tendsto_const_nhds.add regularizer_tendsto) (by simpa using hsp))
  have hlim : p * ((Real.sqrt q + 0) / (Real.sqrt p + 0)) =
      Real.sqrt p * Real.sqrt q := by
    simp only [add_zero]
    nth_rw 1 [← Real.sq_sqrt hp]
    field_simp
  rw [hlim] at ht
  exact ht

/-- The measurable regularized square-root ratio attains the affinity
in the limit, with a constant integrable domination bound. -/
theorem tendsto_integral_regularized_root_tests
    {Z : Type*} [MeasurableSpace Z] (ρ : Measure Z) [IsFiniteMeasure ρ]
    (P Q : Z → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (hPbound : ∀ z, 0 ≤ P z ∧ P z ≤ 1)
    (hQbound : ∀ z, 0 ≤ Q z ∧ Q z ≤ 1) :
    Tendsto (fun n => ∫ z,
      (P z * ((Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n)) +
       Q z * ((Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n))⁻¹) / 2 ∂ρ)
      atTop (𝓝 (∫ z, Real.sqrt (P z) * Real.sqrt (Q z) ∂ρ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
  · intro n
    exact ((hP.mul ((hQ.sqrt.add_const _).div (hP.sqrt.add_const _))).add
      (hQ.mul ((hQ.sqrt.add_const _).div (hP.sqrt.add_const _)).inv)).div_const 2
      |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro z
    have hp0 := (hPbound z).1
    have hq0 := (hQbound z).1
    have hd0 := regularizer_pos n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_div]
    have h1 := weighted_ratio_le_two (P z) (Q z) (regularizer n)
      (hPbound z).1 (hPbound z).2 (hQbound z).1 (hQbound z).2
      (regularizer_pos n) (regularizer_le_one n)
    have h2 := weighted_ratio_le_two (Q z) (P z) (regularizer n)
      (hQbound z).1 (hQbound z).2 (hPbound z).1 (hPbound z).2
      (regularizer_pos n) (regularizer_le_one n)
    linarith
  · apply Eventually.of_forall
    intro z
    have h1 := weighted_ratio_tendsto (P z) (Q z) (hPbound z).1
    have h2 := weighted_ratio_tendsto (Q z) (P z) (hQbound z).1
    have ht := (h1.add h2).div_const 2
    convert ht using 1
    · ext n
      rw [inv_div]
    · congr 1
      ring

section Compact

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]

/-- L1 approximation by continuous functions while preserving fixed
strictly positive lower and upper bounds. -/
theorem exists_continuous_Icc_integral_sub_le
    (ρ : Measure Z) [IsFiniteMeasure ρ]
    (f : Z → ℝ) (hf : Integrable f ρ)
    (c C : ℝ) (hcC : c ≤ C)
    (hfbound : ∀ z, c ≤ f z ∧ f z ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ g : C(Z, ℝ), (∀ z, c ≤ g z ∧ g z ≤ C) ∧
      (∫ z, ‖f z - g z‖ ∂ρ) ≤ η := by
  obtain ⟨g, hg, _⟩ := hf.exists_boundedContinuous_integral_sub_le hη
  let g' : C(Z, ℝ) :=
    ⟨fun z => max c (min C (g z)), continuous_const.max (continuous_const.min g.continuous)⟩
  refine ⟨g', ?_, ?_⟩
  · intro z
    exact ⟨le_max_left _ _, max_le hcC (min_le_left _ _)⟩
  · have hgi : Integrable g ρ := g.integrable ρ
    have hg'i : Integrable g' ρ := (BoundedContinuousFunction.mkOfCompact g').integrable ρ
    apply le_trans (integral_mono (hf.sub hg'i).norm (hf.sub hgi).norm ?_) hg
    intro z
    change ‖f z - max c (min C (g z))‖ ≤ ‖f z - g z‖
    simpa only [Real.norm_eq_abs, abs_sub_comm (f z)] using
      abs_clip_sub_le c C (g z) (f z) (hfbound z).1 (hfbound z).2

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] in
private theorem integrable_of_Icc (ρ : Measure Z) [IsFiniteMeasure ρ]
    (f : Z → ℝ) (hf : Measurable f) (c C : ℝ) (hc : 0 < c)
    (hfbound : ∀ z, c ≤ f z ∧ f z ≤ C) : Integrable f ρ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    simpa [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hfbound z).1)] using (hfbound z).2)

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] in
private theorem inverse_integrable_of_Ici (ρ : Measure Z) [IsFiniteMeasure ρ]
    (f : Z → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 < c)
    (hfbound : ∀ z, c ≤ f z) : Integrable (fun z => (f z)⁻¹) ρ := by
  apply Integrable.mono' (integrable_const c⁻¹) hf.inv.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le (hfbound z)))]
  exact inv_le_inv₀ (hc.trans_le (hfbound z)) hc |>.mpr (hfbound z)

/-- Approximating a positive bounded measurable test by continuous
positive tests also approximates its reciprocal integral. -/
theorem exists_continuous_affinityTest_le
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Z → ℝ) (hf : Measurable f)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hfbound : ∀ z, c ≤ f z ∧ f z ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ g : C(Z, ℝ), (∀ z, 0 < g z) ∧
      affinityTest μ ν g ≤ affinityTest μ ν f + η := by
  let L : ℝ := (c * c)⁻¹
  have hL : 0 ≤ L := le_of_lt (inv_pos.mpr (mul_pos hc hc))
  let δ : ℝ := η / (1 + L)
  have hδ : 0 < δ := div_pos hη (by positivity)
  obtain ⟨g, hgbound, hgδ⟩ := exists_continuous_Icc_integral_sub_le (μ + ν) f
    (integrable_of_Icc (μ + ν) f hf c C hc hfbound) c C hcC hfbound δ hδ
  refine ⟨g, (fun z => hc.trans_le (hgbound z).1), ?_⟩
  have hμle : μ ≤ μ + ν := Measure.le_add_right le_rfl
  have hνle : ν ≤ μ + ν := Measure.le_add_left le_rfl
  have hfi : Integrable f (μ + ν) := integrable_of_Icc _ f hf c C hc hfbound
  have hgi : Integrable g (μ + ν) := (BoundedContinuousFunction.mkOfCompact g).integrable _
  have hdiff : Integrable (fun z => ‖f z - g z‖) (μ + ν) := (hfi.sub hgi).norm
  have hδμ : (∫ z, ‖f z - g z‖ ∂μ) ≤ δ :=
    (integral_mono_measure hμle (Eventually.of_forall (fun z => norm_nonneg _)) hdiff).trans hgδ
  have hδν : (∫ z, ‖f z - g z‖ ∂ν) ≤ δ :=
    (integral_mono_measure hνle (Eventually.of_forall (fun z => norm_nonneg _)) hdiff).trans hgδ
  have hfμ := hfi.mono_measure hμle
  have hgμ := hgi.mono_measure hμle
  have hfνinv := inverse_integrable_of_Ici ν f hf c hc (fun z => (hfbound z).1)
  have hgνinv := inverse_integrable_of_Ici ν g g.continuous.measurable c hc
    (fun z => (hgbound z).1)
  have hμcost : (∫ z, g z ∂μ) ≤ (∫ z, f z ∂μ) + δ := by
    have hnorm := norm_integral_le_integral_norm (fun z => g z - f z) (μ := μ)
    rw [integral_sub hgμ hfμ, Real.norm_eq_abs] at hnorm
    have hnorm' : (∫ z, ‖g z - f z‖ ∂μ) = ∫ z, ‖f z - g z‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => norm_sub_rev _ _)
    rw [hnorm'] at hnorm
    have hle := le_abs_self ((∫ z, g z ∂μ) - ∫ z, f z ∂μ)
    linarith
  have hνcost : (∫ z, (g z)⁻¹ ∂ν) ≤ (∫ z, (f z)⁻¹ ∂ν) + L * δ := by
    have hnorm := norm_integral_le_integral_norm (fun z => (g z)⁻¹ - (f z)⁻¹) (μ := ν)
    rw [integral_sub hgνinv hfνinv, Real.norm_eq_abs] at hnorm
    have hbound : (∫ z, ‖(g z)⁻¹ - (f z)⁻¹‖ ∂ν) ≤
        L * ∫ z, ‖f z - g z‖ ∂ν := by
      rw [← integral_const_mul]
      apply integral_mono (hgνinv.sub hfνinv).norm ((hdiff.mono_measure hνle).const_mul L)
      intro z
      simpa only [Real.norm_eq_abs, abs_sub_comm (g z)] using
        inverse_lipschitz_on_Ici c (g z) (f z) hc (hgbound z).1 (hfbound z).1
    have hmul := mul_le_mul_of_nonneg_left hδν hL
    have hle := le_abs_self ((∫ z, (g z)⁻¹ ∂ν) - ∫ z, (f z)⁻¹ ∂ν)
    linarith
  have hcancel : δ + L * δ = η := by
    dsimp [δ]
    field_simp
  unfold affinityTest
  linarith

private theorem ratio_bounds (p q d : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hd : 0 < d) :
    d / (1 + d) ≤ (Real.sqrt q + d) / (Real.sqrt p + d) ∧
      (Real.sqrt q + d) / (Real.sqrt p + d) ≤ (1 + d) / d := by
  have hsp : Real.sqrt p ≤ 1 := by nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hsq : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  have hden : 0 < Real.sqrt p + d := by positivity
  constructor
  · calc
      d / (1 + d) ≤ (Real.sqrt q + d) / (1 + d) :=
        div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg q]) (by positivity)
      _ ≤ (Real.sqrt q + d) / (Real.sqrt p + d) :=
        div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  · calc
      _ ≤ (1 + d) / (Real.sqrt p + d) := by gcongr
      _ ≤ (1 + d) / d := div_le_div_of_nonneg_left (by positivity) hd
        (by linarith [Real.sqrt_nonneg p])

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] in
/-- Positive bounded measurable tests approximate the actual Hellinger
affinity from above. The regularized RN square-root ratios are explicit. -/
theorem exists_measurable_affinityTest_lt
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : ℝ) (hη : 0 < η) :
    ∃ (f : Z → ℝ) (c C : ℝ), Measurable f ∧ 0 < c ∧ c ≤ C ∧
      (∀ z, c ≤ f z ∧ f z ≤ C) ∧ affinityTest μ ν f < affinity μ ν + η := by
  let P : Z → ℝ := fun z => min (μ.rnDeriv (μ + ν) z).toReal 1
  let Q : Z → ℝ := fun z => min (ν.rnDeriv (μ + ν) z).toReal 1
  have hPm : Measurable P := (Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const
  have hQm : Measurable Q := (Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const
  have hPb : ∀ z, 0 ≤ P z ∧ P z ≤ 1 := fun z =>
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hQb : ∀ z, 0 ≤ Q z ∧ Q z ≤ 1 := fun z =>
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hμle : μ ≤ μ + ν := Measure.le_add_right le_rfl
  have hνle : ν ≤ μ + ν := Measure.le_add_left le_rfl
  have hμ : μ ≪ μ + ν := hμle.absolutelyContinuous
  have hν : ν ≪ μ + ν := hνle.absolutelyContinuous
  have hPeq : P =ᵐ[μ + ν] fun z => (μ.rnDeriv (μ + ν) z).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hμle] with z hz
    exact min_eq_left (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hz)
  have hQeq : Q =ᵐ[μ + ν] fun z => (ν.rnDeriv (μ + ν) z).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hνle] with z hz
    exact min_eq_left (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hz)
  let F : ℕ → Z → ℝ := fun n z =>
    (Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n)
  have hFm : ∀ n, Measurable (F n) := fun n =>
    (hQm.sqrt.add_const _).div (hPm.sqrt.add_const _)
  have hFb : ∀ n z,
      regularizer n / (1 + regularizer n) ≤ F n z ∧
        F n z ≤ (1 + regularizer n) / regularizer n := by
    intro n z
    exact ratio_bounds (P z) (Q z) (regularizer n)
      (hPb z).1 (hPb z).2 (hQb z).1 (hQb z).2 (regularizer_pos n)
  have hcpos : ∀ n, 0 < regularizer n / (1 + regularizer n) := fun n => by
    have hd := regularizer_pos n
    positivity
  have hcC : ∀ n, regularizer n / (1 + regularizer n) ≤
      (1 + regularizer n) / regularizer n := by
    intro n
    calc
      _ ≤ 1 := (div_le_one (by have hd := regularizer_pos n; positivity)).mpr (by linarith)
      _ ≤ _ := (one_le_div (regularizer_pos n)).mpr (by linarith)
  have hcost : ∀ n,
      (∫ z, (P z * F n z + Q z * (F n z)⁻¹) / 2 ∂(μ + ν)) =
        affinityTest μ ν (F n) := by
    intro n
    have hfμ := integrable_of_Icc μ (F n) (hFm n) _ _ (hcpos n) (hFb n)
    have hfinvν := inverse_integrable_of_Ici ν (F n) (hFm n) _ (hcpos n)
      (fun z => (hFb n z).1)
    have hiP := (integrable_toReal_rnDeriv_mul_iff hμ).mpr hfμ
    have hiQ := (integrable_toReal_rnDeriv_mul_iff hν).mpr hfinvν
    have hcongr :
        (fun z => (P z * F n z + Q z * (F n z)⁻¹) / 2) =ᵐ[μ + ν]
        (fun z => ((μ.rnDeriv (μ + ν) z).toReal * F n z +
          (ν.rnDeriv (μ + ν) z).toReal * (F n z)⁻¹) / 2) := by
      filter_upwards [hPeq, hQeq] with z hp hq
      rw [hp, hq]
    rw [integral_congr_ae hcongr, integral_div, integral_add hiP hiQ,
      integral_toReal_rnDeriv_mul hμ, integral_toReal_rnDeriv_mul hν]
    rfl
  have hlimitEq : (∫ z, Real.sqrt (P z) * Real.sqrt (Q z) ∂(μ + ν)) = affinity μ ν := by
    rw [affinity_integral]
    apply integral_congr_ae
    filter_upwards [hPeq, hQeq] with z hp hq
    rw [hp, hq]
  have ht := tendsto_integral_regularized_root_tests (μ + ν) P Q hPm hQm hPb hQb
  change Tendsto (fun n => ∫ z, (P z * F n z + Q z * (F n z)⁻¹) / 2 ∂(μ + ν))
    atTop (𝓝 _) at ht
  simp_rw [hcost, hlimitEq] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 (affinity μ ν + η) (by linarith)).exists
  exact ⟨F n, _, _, hFm n, hcpos n, hcC n, hFb n, hn⟩

/-- Continuous strictly positive tests approximate affinity from above. -/
theorem exists_continuous_affinityTest_lt
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : ℝ) (hη : 0 < η) :
    ∃ g : C(Z, ℝ), (∀ z, 0 < g z) ∧ affinityTest μ ν g < affinity μ ν + η := by
  obtain ⟨f, c, C, hf, hc, hcC, hfb, hfsmall⟩ :=
    exists_measurable_affinityTest_lt μ ν (η / 2) (by positivity)
  obtain ⟨g, hgpos, hgsmall⟩ :=
    exists_continuous_affinityTest_le μ ν f hf c C hc hcC hfb (η / 2) (by positivity)
  exact ⟨g, hgpos, by linarith⟩

/-- Every continuous strictly positive test bounds affinity from above. -/
theorem affinity_le_continuous_affinityTest
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : C(Z, ℝ)) (hg : ∀ z, 0 < g z) : affinity μ ν ≤ affinityTest μ ν g := by
  apply affinity_le_affinityTest_of_integrable μ ν g hg
  · exact (BoundedContinuousFunction.mkOfCompact g).integrable μ
  · let ginv : C(Z, ℝ) := ⟨fun z => (g z)⁻¹,
      g.continuous.inv₀ (fun z => (hg z).ne')⟩
    exact (BoundedContinuousFunction.mkOfCompact ginv).integrable ν

/-- A variational characterization using continuous positive tests.
This strict-sublevel form also directly yields weak upper semicontinuity. -/
theorem affinity_lt_iff_exists_continuous_test
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    affinity μ ν < t ↔
      ∃ g : C(Z, ℝ), (∀ z, 0 < g z) ∧ affinityTest μ ν g < t := by
  constructor
  · intro h
    obtain ⟨g, hg, hsmall⟩ := exists_continuous_affinityTest_lt μ ν
      (t - affinity μ ν) (sub_pos.mpr h)
    exact ⟨g, hg, by linarith⟩
  · rintro ⟨g, hg, hsmall⟩
    exact (affinity_le_continuous_affinityTest μ ν g hg).trans_lt hsmall

/-- The functional of each fixed strictly positive continuous test is
jointly continuous for weak convergence of probabilities. -/
theorem continuous_affinityTest_probability
    (g : C(Z, ℝ)) (hg : ∀ z, 0 < g z) :
    Continuous (fun p : ProbabilityMeasure Z × ProbabilityMeasure Z =>
      affinityTest (p.1 : Measure Z) (p.2 : Measure Z) g) := by
  let ginv : C(Z, ℝ) := ⟨fun z => (g z)⁻¹,
    g.continuous.inv₀ (fun z => (hg z).ne')⟩
  exact ((ProbabilityMeasure.continuous_integral_continuousMap g).comp continuous_fst |>.add
    ((ProbabilityMeasure.continuous_integral_continuousMap ginv).comp continuous_snd)).div_const 2

/-- Hellinger affinity is jointly upper semicontinuous in the weak
topology of probabilities on a compact metric space. -/
theorem upperSemicontinuous_affinity_probability :
    UpperSemicontinuous (fun p : ProbabilityMeasure Z × ProbabilityMeasure Z =>
      affinity (p.1 : Measure Z) (p.2 : Measure Z)) := by
  intro p t ht
  obtain ⟨g, hg, hgt⟩ :=
    (affinity_lt_iff_exists_continuous_test (p.1 : Measure Z) (p.2 : Measure Z) t).mp ht
  have hcont := continuous_affinityTest_probability g hg
  filter_upwards [(hcont.tendsto p).eventually (gt_mem_nhds hgt)] with q hq
  exact (affinity_le_continuous_affinityTest (q.1 : Measure Z) (q.2 : Measure Z) g hg).trans_lt hq

/-- The continuous-test infimum form of the variational identity. -/
theorem affinity_eq_iInf_continuous_tests
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    affinity μ ν = ⨅ g : {g : C(Z, ℝ) // ∀ z, 0 < g z}, affinityTest μ ν g.1 := by
  letI : Nonempty {g : C(Z, ℝ) // ∀ z, 0 < g z} :=
    ⟨⟨1, by intro z; norm_num⟩⟩
  have hbb : BddBelow (Set.range
      (fun g : {g : C(Z, ℝ) // ∀ z, 0 < g z} => affinityTest μ ν g.1)) := by
    refine ⟨affinity μ ν, ?_⟩
    rintro t ⟨g, rfl⟩
    exact affinity_le_continuous_affinityTest μ ν g.1 g.2
  apply le_antisymm
  · apply le_ciInf
    intro g
    exact affinity_le_continuous_affinityTest μ ν g.1 g.2
  · apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨g, hg, hsmall⟩ := exists_continuous_affinityTest_lt μ ν η hη
    exact (ciInf_le hbb ⟨g, hg⟩).trans hsmall.le

/-- The affinity is measurable for the Borel structure of the weak
probability topology. -/
theorem measurable_affinity_probability_borel :
    @Measurable (ProbabilityMeasure Z × ProbabilityMeasure Z) ℝ
      (borel (ProbabilityMeasure Z × ProbabilityMeasure Z)) (borel ℝ)
      (fun p => affinity (p.1 : Measure Z) (p.2 : Measure Z)) := by
  letI : MeasurableSpace (ProbabilityMeasure Z × ProbabilityMeasure Z) := borel _
  letI : BorelSpace (ProbabilityMeasure Z × ProbabilityMeasure Z) := ⟨rfl⟩
  exact upperSemicontinuous_affinity_probability.measurable

end Compact

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.exists_continuous_Icc_integral_sub_le
#print axioms MeasureEquivalenceHellinger.affinity_le_affinityTest_of_integrable
#print axioms MeasureEquivalenceHellinger.tendsto_integral_regularized_root_tests
#print axioms MeasureEquivalenceHellinger.exists_measurable_affinityTest_lt
#print axioms MeasureEquivalenceHellinger.exists_continuous_affinityTest_lt
#print axioms MeasureEquivalenceHellinger.affinity_lt_iff_exists_continuous_test
#print axioms MeasureEquivalenceHellinger.upperSemicontinuous_affinity_probability
#print axioms MeasureEquivalenceHellinger.affinity_eq_iInf_continuous_tests
#print axioms MeasureEquivalenceHellinger.measurable_affinity_probability_borel
