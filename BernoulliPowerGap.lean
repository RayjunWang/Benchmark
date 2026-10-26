import BernoulliSupportGap
import PowerDifference

/-! Transfer of the actual Bernoulli Hilbert gap to nonnegative bounded functions
supported on a set of probability at most one half. The power estimate uses
an absorption inequality, so no unproved interpolation theorem is assumed. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace BenchmarkShift

lemma bounded_power (f : Point → ℝ) (hn : ∀ x, 0 ≤ f x)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (q : ℝ) (hq : 0 ≤ q) :
    ∃ B : ℝ, ∀ x, |(f x) ^ q| ≤ B := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨(max B 0) ^ q, fun x => ?_⟩
  rw [abs_of_nonneg (Real.rpow_nonneg (hn x) _)]
  exact Real.rpow_le_rpow (hn x) ((le_abs_self _).trans ((hB x).trans (le_max_left _ _))) hq

lemma bounded_integrable (f : Point → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) : Integrable f bernoulli := by
  obtain ⟨B, hB⟩ := hb
  exact (MemLp.of_bound (p := (1 : ℝ≥0∞)) hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)).integrable le_rfl

lemma bounded_power_integrable (f : Point → ℝ) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x => f x ^ q) bernoulli :=
  bounded_integrable _ ((Real.continuous_rpow_const hq).measurable.comp hf)
    (bounded_power f hn hb q hq)

lemma bounded_difference (f : Point → ℝ) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (t : Point → Point) : ∃ B : ℝ, ∀ x, |f (t x) - f x| ≤ B := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨2 * B, fun x => (abs_sub _ _).trans (by linarith [hB (t x), hB x])⟩

lemma bounded_difference_power_integrable (f : Point → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (t : Point → Point) (ht : Measurable t)
    (p : ℝ) (hp : 0 ≤ p) : Integrable (fun x => |f (t x) - f x| ^ p) bernoulli := by
  apply bounded_power_integrable _ ((hf.comp ht).sub hf).abs (fun x => abs_nonneg _) _ p hp
  simpa only [abs_abs] using bounded_difference f hb t

lemma integral_shift (g : Group) (f : Point → ℝ) :
    (∫ x, f (shift g x) ∂bernoulli) = ∫ x, f x ∂bernoulli := by
  have hfun : shift g = (MeasurableEquiv.piCongrLeft (fun _ : Group => Bool) (Equiv.mulLeft g)) := by
    funext x h
    obtain ⟨k, rfl⟩ := (Equiv.mulLeft g).surjective h
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [shift]
  exact (measurePreserving_shift g).integral_comp
    (hfun ▸ (MeasurableEquiv.piCongrLeft (fun _ : Group => Bool) (Equiv.mulLeft g)).measurableEmbedding) f

def powerGapConstant (p : ℝ) : ℝ :=
  if p ≤ 2 then 16 else 32 * BenchmarkPowerDifference.powerErrorConstant p

lemma powerGapConstant_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ powerGapConstant p := by
  unfold powerGapConstant
  split_ifs with h
  · norm_num
  · exact mul_nonneg (by norm_num)
      (BenchmarkPowerDifference.powerErrorConstant_nonneg p (by linarith))

theorem supported_integral_power_gap (p : ℝ) (hp : 0 < p)
    (f : Point → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hsmall : bernoulli.real {x | f x ≠ 0} ≤ 1 / 2) :
    (∫ x, (f x) ^ p ∂bernoulli) ≤ powerGapConstant p *
      ((∫ x, |f (inverseGeneratorShift 0 x) - f x| ^ p ∂bernoulli) +
       (∫ x, |f (inverseGeneratorShift 1 x) - f x| ^ p ∂bernoulli)) := by
  let h : Point → ℝ := fun x => f x ^ (p / 2)
  have hq : 0 < p / 2 := by linarith
  have hh : Measurable h := (Real.continuous_rpow_const hq.le).measurable.comp hf
  have hhb := bounded_power f hn hb (p / 2) hq.le
  have hhs : {x | h x ≠ 0} = {x | f x ≠ 0} := by
    ext x
    exact Real.rpow_ne_zero (hn x) hq.ne'
  have hg := supported_integral_sq_gap h hh hhb (hhs ▸ hsmall)
  have hsq (x : Point) : h x ^ 2 = f x ^ p := by
    dsimp only [h]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hn x)]
    congr 1
    norm_num
  simp_rw [hsq] at hg
  by_cases hp2 : p ≤ 2
  · have hbound (i : Fin 2) :
        (∫ x, (h (inverseGeneratorShift i x) - h x) ^ 2 ∂bernoulli) ≤
          ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
      apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
        (bounded_difference_power_integrable f hf hb _ (continuous_shift _).measurable p hp.le)
      apply ae_of_all
      intro x
      have he := BenchmarkPowerDifference.abs_sub_rpow_le
        (hn (inverseGeneratorShift i x)) (hn x) hq.le (by linarith : p / 2 ≤ 1)
      have h2 := (sq_le_sq₀ (abs_nonneg _)
        (Real.rpow_nonneg (abs_nonneg (f (inverseGeneratorShift i x) - f x)) _)).mpr he
      have heq : (|f (inverseGeneratorShift i x) - f x| ^ (p / 2)) ^ 2 =
          |f (inverseGeneratorShift i x) - f x| ^ p := by
        rw [← Real.rpow_natCast (|f (inverseGeneratorShift i x) - f x| ^ (p / 2)) 2,
          ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        norm_num
      rw [sq_abs, heq] at h2
      exact h2
    have h0 := hbound 0
    have h1 := hbound 1
    simp only [powerGapConstant, if_pos hp2]
    linarith
  · have hp2' : 2 ≤ p := le_of_lt (lt_of_not_ge hp2)
    let C := BenchmarkPowerDifference.powerErrorConstant p
    let I := ∫ x, f x ^ p ∂bernoulli
    have hI : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (hn x) _
    have hC : 0 ≤ C := BenchmarkPowerDifference.powerErrorConstant_nonneg p hp2'
    have hbound (i : Fin 2) :
        (∫ x, (h (inverseGeneratorShift i x) - h x) ^ 2 ∂bernoulli) ≤
          (1 / 128 : ℝ) * I + C *
            ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
      have hfpi := bounded_power_integrable f hf hn hb p hp.le
      have hs : Integrable (fun x => f (inverseGeneratorShift i x) ^ p) bernoulli :=
        bounded_power_integrable _ (hf.comp (continuous_shift _).measurable)
          (fun x => hn _) (by
            obtain ⟨B, hB⟩ := hb
            exact ⟨B, fun x => hB _⟩) p hp.le
      have hd := bounded_difference_power_integrable f hf hb (inverseGeneratorShift i)
        (continuous_shift (letterGroup (i, true))⁻¹).measurable p hp.le
      have hr := ((hs.add hfpi).const_mul (1 / 256 : ℝ)).add (hd.const_mul C)
      have hle := integral_mono_of_nonneg (ae_of_all _ fun x =>
        sq_nonneg (h (inverseGeneratorShift i x) - h x)) hr (ae_of_all _ fun x => ?_)
      · change (∫ x, (h (inverseGeneratorShift i x) - h x) ^ 2 ∂bernoulli) ≤
          ∫ x, (1 / 256 : ℝ) * (f (inverseGeneratorShift i x) ^ p + f x ^ p) +
            C * |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli at hle
        have hadd := integral_add ((hs.add hfpi).const_mul (1 / 256 : ℝ)) (hd.const_mul C)
        have hadd' := integral_add hs hfpi
        simp only [Pi.add_apply] at hadd hadd'
        rw [hadd, integral_const_mul, hadd', integral_const_mul] at hle
        have hshift : (∫ x, f (inverseGeneratorShift i x) ^ p ∂bernoulli) = I :=
          integral_shift _ (fun x => f x ^ p)
        rw [hshift] at hle
        dsimp only [I] at hle ⊢
        linarith
      · have he := BenchmarkPowerDifference.power_difference_sq_le
          (hn (inverseGeneratorShift i x)) (hn x) hp2'
        have hm : (max (f (inverseGeneratorShift i x)) (f x)) ^ p ≤
            f (inverseGeneratorShift i x) ^ p + f x ^ p := by
          rcases le_total (f (inverseGeneratorShift i x)) (f x) with ht | ht
          · rw [max_eq_right ht]
            exact le_add_of_nonneg_left (Real.rpow_nonneg (hn _) _)
          · rw [max_eq_left ht]
            exact le_add_of_nonneg_right (Real.rpow_nonneg (hn _) _)
        change (f (inverseGeneratorShift i x) ^ (p / 2) - f x ^ (p / 2)) ^ 2 ≤
          (1 / 256 : ℝ) * (f (inverseGeneratorShift i x) ^ p + f x ^ p) +
            BenchmarkPowerDifference.powerErrorConstant p * |f (inverseGeneratorShift i x) - f x| ^ p
        linarith only [he, hm]
    have h0 := hbound 0
    have h1 := hbound 1
    have hD0 : 0 ≤ ∫ x, |f (inverseGeneratorShift 0 x) - f x| ^ p ∂bernoulli :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    have hD1 : 0 ≤ ∫ x, |f (inverseGeneratorShift 1 x) - f x| ^ p ∂bernoulli :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    simp only [powerGapConstant, if_neg hp2]
    change I ≤ 32 * C * _
    dsimp only [I] at h0 h1 ⊢
    nlinarith

end BenchmarkShift

#print axioms BenchmarkShift.supported_integral_power_gap
