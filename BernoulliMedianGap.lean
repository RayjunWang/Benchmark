import BernoulliPowerGap
import PoincareRadial

/-! A median Poincaré inequality for every finite positive exponent, with an
explicit finite constant, on the actual Bernoulli action of the free group. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkShift

lemma measureReal_le_half {s : Set Point} (h : bernoulli s ≤ 1 / 2) :
    bernoulli.real s ≤ (1 / 2 : ℝ) := by
  have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) h
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hh
  exact hh

lemma positivePart_support (f : Point → ℝ) :
    {x | max (f x) 0 ≠ 0} = {x | 0 < f x} := by
  ext x
  by_cases hx : 0 < f x
  · simp [hx, max_eq_left hx.le, hx.ne']
  · simp [hx, max_eq_right (le_of_not_gt hx)]

lemma bounded_positivePart (f : Point → ℝ) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    ∃ B : ℝ, ∀ x, |max (f x) 0| ≤ B := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B, fun x => ?_⟩
  have h := abs_max_sub_max_le_abs (f x) 0 0
  have h' : |max (f x) 0| ≤ |f x| := by simpa only [max_self, sub_zero] using h
  exact h'.trans (hB x)

theorem median_integral_power_gap (p : ℝ) (hp : 0 < p)
    (f : Point → ℝ) (hf : Measurable f)
    (hm : BenchmarkPoincareRadial.ZeroMedian bernoulli f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    (∫ x, |f x| ^ p ∂bernoulli) ≤ (2 * powerGapConstant p) *
      ((∫ x, |f (inverseGeneratorShift 0 x) - f x| ^ p ∂bernoulli) +
       (∫ x, |f (inverseGeneratorShift 1 x) - f x| ^ p ∂bernoulli)) := by
  let fpos : Point → ℝ := fun x => max (f x) 0
  let fneg : Point → ℝ := fun x => max (-f x) 0
  have hfpos : Measurable fpos := hf.max measurable_const
  have hfneg : Measurable fneg := hf.neg.max measurable_const
  have hnpos (x : Point) : 0 ≤ fpos x := le_max_right _ _
  have hnneg (x : Point) : 0 ≤ fneg x := le_max_right _ _
  have hbpos := bounded_positivePart f hb
  have hbneg := bounded_positivePart (fun x => -f x) (by simpa only [abs_neg] using hb)
  have hsmallpos : bernoulli.real {x | fpos x ≠ 0} ≤ 1 / 2 := by
    rw [positivePart_support]
    apply measureReal_le_half
    simpa only [measure_univ] using hm.2
  have hsmallneg : bernoulli.real {x | fneg x ≠ 0} ≤ 1 / 2 := by
    rw [positivePart_support]
    have heq : {x | 0 < -f x} = {x | f x < 0} := by ext x; simp only [mem_setOf_eq, neg_pos]
    rw [heq]
    apply measureReal_le_half
    simpa only [measure_univ] using hm.1
  have hgpos := supported_integral_power_gap p hp fpos hfpos hnpos hbpos hsmallpos
  have hgneg := supported_integral_power_gap p hp fneg hfneg hnneg hbneg hsmallneg
  have hsplit (x : Point) : |f x| ^ p = fpos x ^ p + fneg x ^ p := by
    dsimp only [fpos, fneg]
    by_cases hx : 0 ≤ f x
    · simp [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
        Real.zero_rpow hp.ne']
    · have hx' : f x ≤ 0 := (lt_of_not_ge hx).le
      simp [abs_of_nonpos hx', max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'),
        Real.zero_rpow hp.ne']
  have heq : (∫ x, |f x| ^ p ∂bernoulli) =
      (∫ x, fpos x ^ p ∂bernoulli) + ∫ x, fneg x ^ p ∂bernoulli := by
    simp_rw [hsplit]
    exact integral_add (bounded_power_integrable fpos hfpos hnpos hbpos p hp.le)
      (bounded_power_integrable fneg hfneg hnneg hbneg p hp.le)
  have hbound (g : Point → ℝ) (hg : ∀ x y, |g x - g y| ≤ |f x - f y|) (i : Fin 2) :
      (∫ x, |g (inverseGeneratorShift i x) - g x| ^ p ∂bernoulli) ≤
        ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
    apply integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (bounded_difference_power_integrable f hf hb _ (continuous_shift _).measurable p hp.le)
    exact ae_of_all _ fun x => Real.rpow_le_rpow (abs_nonneg _) (hg _ _) hp.le
  have hpbound (i : Fin 2) := hbound fpos (fun x y => abs_max_sub_max_le_abs _ _ _) i
  have hnbound (i : Fin 2) :
      (∫ x, |fneg (inverseGeneratorShift i x) - fneg x| ^ p ∂bernoulli) ≤
        ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
    apply hbound fneg _ i
    intro x y
    simpa only [neg_sub_neg, abs_sub_comm] using abs_max_sub_max_le_abs (-f x) (-f y) 0
  have hK := powerGapConstant_nonneg hp
  rw [heq]
  have hpm := mul_le_mul_of_nonneg_left (add_le_add (hpbound 0) (hpbound 1)) hK
  have hnm := mul_le_mul_of_nonneg_left (add_le_add (hnbound 0) (hnbound 1)) hK
  linarith

theorem scalarPoincare_inverseGenerators (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    BenchmarkPoincareRadial.ScalarPoincareBound p bernoulli inverseGeneratorShift
      (ENNReal.ofReal (2 * powerGapConstant p.toReal)) := by
  intro f hf hm hb
  have hp0 : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hg := median_integral_power_gap p.toReal hp0 f hf hm hb
  have hfi : Integrable (fun x => |f x| ^ p.toReal) bernoulli := by
    apply bounded_power_integrable _ hf.abs (fun x => abs_nonneg _) _ p.toReal hp0.le
    simpa only [abs_abs] using hb
  have hdi (i : Fin 2) := bounded_difference_power_integrable f hf hb (inverseGeneratorShift i)
    (continuous_shift (letterGroup (i, true))⁻¹).measurable p.toReal hp0.le
  have hleft := ofReal_integral_eq_lintegral_ofReal hfi
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg (f x)) p.toReal)
  have hright (i : Fin 2) := ofReal_integral_eq_lintegral_ofReal (hdi i)
    (ae_of_all _ fun x => Real.rpow_nonneg
      (abs_nonneg (f (inverseGeneratorShift i x) - f x)) p.toReal)
  have hnonneg (i : Fin 2) : 0 ≤
      ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p.toReal ∂bernoulli :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  have he := ENNReal.ofReal_le_ofReal hg
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (powerGapConstant_nonneg hp0)),
    ENNReal.ofReal_add (hnonneg 0) (hnonneg 1), hleft, hright 0, hright 1] at he
  simpa only [BenchmarkRadialEnergy.scalarEnergy, Fin.sum_univ_two] using he

end BenchmarkShift

#print axioms BenchmarkShift.scalarPoincare_inverseGenerators
