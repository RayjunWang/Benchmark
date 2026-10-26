import BernoulliIsoperimetry
import Mathlib.MeasureTheory.Order.Group.Lattice

/-! The Hilbert gap for functions whose support has at most half the probability. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace BenchmarkShift

theorem bernoulli_supported_L2_gap (s : Set Point) (hs : MeasurableSet s)
    (hsmall : bernoulli.real s ≤ 1 / 2) (u : BernoulliL2)
    (hu : ∀ᵐ x ∂bernoulli, x ∉ s → u x = 0) :
    ‖u‖ ^ 2 ≤ 16 *
      (‖koopman (letterGroup (0, true)) u - u‖ ^ 2 +
        ‖koopman (letterGroup (1, true)) u - u‖ ^ 2) := by
  have hi : ⟪indicatorL2 s hs, u⟫_ℝ = ∫ x, u x ∂bernoulli := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
      (hμs := measure_ne_top bernoulli s) (c := (1 : ℝ)))] with x hx hy
    simp only [RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    change indicatorConstLp 2 hs (measure_ne_top bernoulli s) (1 : ℝ) x * u x = u x
    rw [hy]
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs, hx hxs]
  have hcs := real_inner_mul_inner_self_le (indicatorL2 s hs) u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sq_indicatorL2, hi] at hcs
  have hm : (∫ x, u x ∂bernoulli) ^ 2 ≤ (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
    have hb := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u‖)
    nlinarith
  have hg := bernoulli_variance_gap u
  linarith

lemma norm_sq_L2_eq_integral (u : BernoulliL2) :
    ‖u‖ ^ 2 = ∫ x, (u x) ^ 2 ∂bernoulli := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext x
  simp [pow_two]

def inverseGeneratorShift (i : Fin 2) : Point → Point := shift (letterGroup (i, true))⁻¹

theorem supported_integral_sq_gap (f : Point → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hsmall : bernoulli.real {x | f x ≠ 0} ≤ 1 / 2) :
    (∫ x, (f x) ^ 2 ∂bernoulli) ≤ 16 *
      ((∫ x, (f (inverseGeneratorShift 0 x) - f x) ^ 2 ∂bernoulli) +
       (∫ x, (f (inverseGeneratorShift 1 x) - f x) ^ 2 ∂bernoulli)) := by
  obtain ⟨B, hB⟩ := hb
  have hmem : MemLp f 2 bernoulli := MemLp.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)
  let u : BernoulliL2 := hmem.toLp f
  have hu : (u : Point → ℝ) =ᵐ[bernoulli] f := hmem.coeFn_toLp
  have hs : MeasurableSet {x | f x ≠ 0} := (measurableSet_eq_fun hf measurable_const).compl
  have hsupport : ∀ᵐ x ∂bernoulli, x ∉ {x | f x ≠ 0} → u x = 0 := by
    filter_upwards [hu] with x hx
    simpa only [mem_setOf_eq, not_not, hx] using (fun h : f x = 0 => h)
  have hg := bernoulli_supported_L2_gap {x | f x ≠ 0} hs hsmall u hsupport
  have hn : ‖u‖ ^ 2 = ∫ x, (f x) ^ 2 ∂bernoulli := by
    rw [norm_sq_L2_eq_integral]
    exact integral_congr_ae (hu.fun_comp fun y : ℝ => y ^ 2)
  have hd (i : Fin 2) : ‖koopman (letterGroup (i, true)) u - u‖ ^ 2 =
      ∫ x, (f (inverseGeneratorShift i x) - f x) ^ 2 ∂bernoulli := by
    rw [norm_sq_L2_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (koopman (letterGroup (i, true)) u) u,
      koopman_ae (letterGroup (i, true)) u, hu,
      (measurePreserving_shift (letterGroup (i, true))⁻¹).quasiMeasurePreserving.ae hu]
      with x hx hy hz hw
    change (koopman (letterGroup (i, true)) u - u) x ^ 2 = _
    rw [hx, Pi.sub_apply, hy, hz, hw]
    rfl
  rwa [hn, hd, hd] at hg

end BenchmarkShift

#print axioms BenchmarkShift.supported_integral_sq_gap
