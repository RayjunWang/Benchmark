import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Concrete weighted-exponential Hilbert snowflake on the positive half-line.
This file is developed separately from the frozen Gaussian proof sources.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureEquivalenceSnowflake

noncomputable def oscillation (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I * (s * t : ℝ)) - 1

noncomputable def raw (p t s : ℝ) : ℂ :=
  (s ^ (-(1 + p) / 2) : ℝ) • oscillation t s

noncomputable def halfLine : Measure ℝ := volume.restrict (Ioi 0)

lemma measurable_oscillation (t : ℝ) : Measurable (oscillation t) := by
  unfold oscillation
  fun_prop

lemma measurable_raw (p t : ℝ) : Measurable (raw p t) := by
  unfold raw
  exact (measurable_id.pow_const _).smul (measurable_oscillation t)

lemma oscillation_norm_le_linear (t s : ℝ) : ‖oscillation t s‖ ≤ ‖s * t‖ :=
  Real.norm_exp_I_mul_ofReal_sub_one_le

lemma oscillation_norm_le_two (t s : ℝ) : ‖oscillation t s‖ ≤ 2 := by
  calc
    _ ≤ ‖Complex.exp (Complex.I * (s * t : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num

lemma raw_norm_sq (p t s : ℝ) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 = ‖oscillation t s‖ ^ 2 * s ^ (-1 - p) := by
  have hw : (s ^ (-(1 + p) / 2) : ℝ) ^ 2 = s ^ (-1 - p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    norm_num
    ring
  rw [raw, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), mul_pow, hw]
  ring

lemma raw_norm_sq_le_local (p t s : ℝ) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 ≤ t ^ 2 * s ^ (1 - p) := by
  have hn := oscillation_norm_le_linear t s
  have hsq : ‖oscillation t s‖ ^ 2 ≤ (s * t) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hp : s ^ 2 * s ^ (-1 - p) = s ^ (1 - p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    congr 1
    norm_num
    ring
  rw [raw_norm_sq p t s hs]
  calc
    _ ≤ (s * t) ^ 2 * s ^ (-1 - p) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs.le _)
    _ = t ^ 2 * (s ^ 2 * s ^ (-1 - p)) := by ring
    _ = t ^ 2 * s ^ (1 - p) := by rw [hp]

lemma raw_norm_sq_le_tail (p t s : ℝ) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 ≤ 4 * s ^ (-1 - p) := by
  rw [raw_norm_sq p t s hs]
  exact mul_le_mul_of_nonneg_right
    (by convert pow_le_pow_left₀ (norm_nonneg _) (oscillation_norm_le_two t s) 2 using 1; norm_num)
    (Real.rpow_nonneg hs.le _)

lemma integrable_raw_norm_sq (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    Integrable (fun s => ‖raw p t s‖ ^ 2) halfLine := by
  have hm := (measurable_raw p t).norm.pow_const 2
  have hlocal : IntegrableOn (fun s => ‖raw p t s‖ ^ 2) (Ioo 0 1) := by
    have hb : IntegrableOn (fun s : ℝ => t ^ 2 * s ^ (1 - p)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)).const_mul _
    refine hb.mono' hm.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact raw_norm_sq_le_local p t s hs.1)
  have htail : IntegrableOn (fun s => ‖raw p t s‖ ^ 2) (Ioi 1) := by
    have hb : IntegrableOn (fun s : ℝ => 4 * s ^ (-1 - p)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hb.mono' hm.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact raw_norm_sq_le_tail p t s (lt_trans zero_lt_one hs))
  change IntegrableOn (fun s => ‖raw p t s‖ ^ 2) (Ioi (0 : ℝ)) volume
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hlocal).union htail

lemma memLp_raw (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    MemLp (raw p t) 2 halfLine :=
  (memLp_two_iff_integrable_sq_norm (measurable_raw p t).aestronglyMeasurable).2
    (integrable_raw_norm_sq p hp0 hp2 t)

noncomputable def embedding (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    Lp ℂ 2 halfLine := (memLp_raw p hp0 hp2 t).toLp (raw p t)

lemma oscillation_norm_neg (t s : ℝ) : ‖oscillation (-t) s‖ = ‖oscillation t s‖ := by
  simp only [oscillation, Complex.norm_exp_I_mul_ofReal_sub_one, mul_neg,
    neg_div, Real.sin_neg, mul_neg, norm_neg]

lemma raw_norm_neg (p t s : ℝ) : ‖raw p (-t) s‖ = ‖raw p t s‖ := by
  simp only [raw, norm_smul, oscillation_norm_neg]

lemma oscillation_sub_factor (t u s : ℝ) :
    oscillation t s - oscillation u s =
      Complex.exp (Complex.I * (s * u : ℝ)) * oscillation (t - u) s := by
  unfold oscillation
  rw [mul_sub, ← Complex.exp_add]
  have he : Complex.I * (s * u : ℝ) + Complex.I * (s * (t - u) : ℝ) =
      Complex.I * (s * t : ℝ) := by push_cast; ring
  rw [he]
  ring

lemma raw_sub_norm (p t u s : ℝ) : ‖raw p t s - raw p u s‖ = ‖raw p (t - u) s‖ := by
  simp only [raw, ← smul_sub, norm_smul]
  rw [oscillation_sub_factor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

noncomputable def energy (p t : ℝ) : ℝ := ∫ s, ‖raw p t s‖ ^ 2 ∂halfLine

lemma energy_neg (p t : ℝ) : energy p (-t) = energy p t := by
  simp only [energy, raw_norm_neg]

lemma raw_norm_sq_dilation (p t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 = t ^ (1 + p) * ‖raw p 1 (t * s)‖ ^ 2 := by
  rw [raw_norm_sq p t s hs, raw_norm_sq p 1 (t * s) (mul_pos ht hs),
    Real.mul_rpow ht.le hs.le]
  have ho : oscillation 1 (t * s) = oscillation t s := by simp [oscillation, mul_comm]
  have ht' : t ^ (1 + p) * t ^ (-1 - p) = (1 : ℝ) := by
    rw [← Real.rpow_add ht]
    have he : (1 + p) + (-1 - p) = 0 := by ring
    rw [he, Real.rpow_zero]
  rw [ho]
  symm
  calc
    _ = (t ^ (1 + p) * t ^ (-1 - p)) * (‖oscillation t s‖ ^ 2 * s ^ (-1 - p)) := by ring
    _ = _ := by rw [ht', one_mul]

lemma energy_pos_dilation (p t : ℝ) (ht : 0 < t) :
    energy p t = t ^ p * energy p 1 := by
  have hraw : (fun s => ‖raw p t s‖ ^ 2) =ᵐ[halfLine]
      (fun s => t ^ (1 + p) * ‖raw p 1 (t * s)‖ ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => raw_norm_sq_dilation p t s ht hs)
  unfold energy
  rw [integral_congr_ae hraw, integral_const_mul]
  change t ^ (1 + p) * (∫ s in Ioi (0 : ℝ), ‖raw p 1 (t * s)‖ ^ 2) = _
  rw [integral_comp_mul_left_Ioi (fun s => ‖raw p 1 s‖ ^ 2) 0 ht]
  simp only [mul_zero, smul_eq_mul]
  have ht' : t ^ (1 + p) * t⁻¹ = t ^ p := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    congr 1
    ring
  rw [← mul_assoc, ht']
  rfl

lemma energy_abs (p : ℝ) (hp0 : 0 < p) (t : ℝ) :
    energy p t = |t| ^ p * energy p 1 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [abs_of_neg ht, ← energy_neg p t]
    exact energy_pos_dilation p (-t) (neg_pos.mpr ht)
  · simp [energy, raw, oscillation, Real.zero_rpow hp0.ne']
  · rw [abs_of_pos ht]
    exact energy_pos_dilation p t ht

lemma energy_one_pos (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) : 0 < energy p 1 := by
  apply (integral_pos_iff_support_of_nonneg (fun s => sq_nonneg _)
    (integrable_raw_norm_sq p hp0 hp2 1)).2
  have hsub : Ioo 0 Real.pi ⊆ Function.support (fun s => ‖raw p 1 s‖ ^ 2) := by
    intro s hs
    change ‖raw p 1 s‖ ^ 2 ≠ 0
    have hsin : 0 < Real.sin (s / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
    have ho : 0 < ‖oscillation 1 s‖ := by
      rw [oscillation, Complex.norm_exp_I_mul_ofReal_sub_one, mul_one, Real.norm_eq_abs]
      exact abs_pos.mpr (mul_ne_zero two_ne_zero hsin.ne')
    rw [raw_norm_sq p 1 s hs.1]
    exact (mul_pos (pow_pos ho _) (Real.rpow_pos_of_pos hs.1 _)).ne'
  have hm : 0 < halfLine (Ioo 0 Real.pi) := by
    rw [halfLine, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr Ioo_subset_Ioi_self, Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr Real.pi_pos
  exact hm.trans_le (measure_mono hsub)

lemma embedding_coe (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    embedding p hp0 hp2 t =ᵐ[halfLine] raw p t :=
  (memLp_raw p hp0 hp2 t).coeFn_toLp

lemma lp_norm_sq (f : Lp ℂ 2 halfLine) : ‖f‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂halfLine := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem embedding_norm_sub_sq (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t u : ℝ) :
    ‖embedding p hp0 hp2 t - embedding p hp0 hp2 u‖ ^ 2 =
      energy p 1 * |t - u| ^ p := by
  rw [lp_norm_sq]
  have hnorm : (fun s => ‖(embedding p hp0 hp2 t - embedding p hp0 hp2 u) s‖ ^ 2)
      =ᵐ[halfLine] (fun s => ‖raw p (t - u) s‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub (embedding p hp0 hp2 t) (embedding p hp0 hp2 u),
      embedding_coe p hp0 hp2 t, embedding_coe p hp0 hp2 u] with s hs ht hu
    simp only [hs, Pi.sub_apply, ht, hu, raw_sub_norm]
  rw [integral_congr_ae hnorm]
  exact (energy_abs p hp0 (t - u)).trans (mul_comm _ _)

theorem embedding_dist (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t u : ℝ) :
    dist (embedding p hp0 hp2 t) (embedding p hp0 hp2 u) =
      Real.sqrt (energy p 1 * |t - u| ^ p) := by
  rw [← embedding_norm_sub_sq p hp0 hp2 t u, Real.sqrt_sq (norm_nonneg _), dist_eq_norm]

theorem continuous_embedding (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) :
    Continuous (embedding p hp0 hp2) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp_rw [embedding_dist]
  have hc : Continuous (fun u : ℝ => Real.sqrt (energy p 1 * |u - t| ^ p)) :=
    Real.continuous_sqrt.comp (continuous_const.mul
      ((continuous_id.sub continuous_const).abs.rpow_const (fun _ => Or.inr hp0.le)))
  simpa only [sub_self, abs_zero, Real.zero_rpow hp0.ne', mul_zero, Real.sqrt_zero]
    using hc.tendsto t

#print axioms memLp_raw
#print axioms energy_one_pos
#print axioms embedding_norm_sub_sq
#print axioms continuous_embedding

end MeasureEquivalenceSnowflake
