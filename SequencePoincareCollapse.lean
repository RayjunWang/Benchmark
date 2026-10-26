import PoincareRadial
import NormalizedTruncation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Sequence-valued homomorphism collapse from scalar Poincaré bounds

The supplied medians and scalar Poincaré bound imply almost-everywhere
ℓp-equivalence to their median sequence. Displacement sequences need only
be summable almost everywhere; their norms need not be integrable.

This proves the analytic implication used in the manuscript. Existence
of real medians and the scalar Poincaré bound for the Bernoulli action are
separate inputs, not claimed here as already formalized theorems.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkSequencePoincare

open BenchmarkPoincareRadial BenchmarkRadialEnergy BenchmarkNormalizedTruncation

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) [IsFiniteMeasure μ]

def prefixVector (f : X → ℕ → ℝ) (m : ℕ → ℝ) (N : ℕ) (x : X) : Vector (I := Fin N) p :=
  WithLp.toLp p (fun i : Fin N => f x i - m i)

lemma measurable_prefixVector (f : X → ℕ → ℝ) (hf : Measurable f) (m : ℕ → ℝ) (N : ℕ) :
    Measurable (prefixVector p f m N) := by
  apply (WithLp.measurable_toLp p _).comp
  exact measurable_pi_lambda _ (fun i => ((measurable_pi_apply (i : ℕ)).comp hf).sub_const _)

lemma prefixVector_energy (hp : p ≠ ∞) (f : X → ℕ → ℝ) (m : ℕ → ℝ) (N : ℕ) (x : X) :
    vectorEnergy p (prefixVector p f m N x) =
      ∑ i ∈ Finset.range N, ENNReal.ofReal (|f x i - m i| ^ p.toReal) := by
  rw [vectorEnergy_eq_sum p hp, Finset.sum_range]
  rfl

theorem ae_summable_centered_of_poincare
    (hp : p ≠ ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hP : ScalarPoincareBound p μ t C)
    (f : X → ℕ → ℝ) (hf : Measurable f) (m : ℕ → ℝ)
    (hm : ∀ i, ZeroMedian μ (fun x => f x i - m i))
    (hdisplacement : ∀ s, ∀ᵐ x ∂μ,
      Summable (fun i => |f (t s x) i - f x i| ^ p.toReal)) :
    ∀ᵐ x ∂μ, Summable (fun i => |f x i - m i| ^ p.toReal) := by
  classical
  let a := fun i x => ENNReal.ofReal (|f x i - m i| ^ p.toReal)
  let c := fun s x => ∑' i, ENNReal.ofReal (|f (t s x) i - f x i| ^ p.toReal)
  let K := ENNReal.ofReal ((2 : ℝ) ^ p.toReal) * C
  have ha : ∀ i, Measurable (a i) := by
    intro i
    exact (((((measurable_pi_apply i).comp hf).sub_const _).abs).pow_const _).ennreal_ofReal
  have hc : ∀ s, Measurable (c s) := by
    intro s
    apply Measurable.ennreal_tsum
    intro i
    exact (((((measurable_pi_apply i).comp (hf.comp (ht s))).sub
      ((measurable_pi_apply i).comp hf)).abs).pow_const _).ennreal_ofReal
  have hcf : ∀ s, ∀ᵐ x ∂μ, c s x ≠ ∞ := by
    intro s
    filter_upwards [hdisplacement s] with x hx
    exact hx.tsum_ofReal_ne_top
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hfinite : ∀ᵐ x ∂μ, (∑' i, a i x) ≠ ∞ := by
    apply ae_finite_tsum_of_unnormalized_energy μ a ha c hc hcf K hK
    intro N n
    let R := ((n : ℝ) + 1) ^ (1 / p.toReal)
    have hR : 0 < R := Real.rpow_pos_of_pos (by positivity) _
    have hq : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    have hRq : R ^ p.toReal = (n : ℝ) + 1 := by
      dsimp [R]
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hq.ne', Real.rpow_one]
    let v := prefixVector p f m N
    have hv := measurable_prefixVector p f hf m N
    have hmed : ∀ i : Fin N, ZeroMedian μ (fun x => v x i) := fun i => hm i
    have htrunc := truncated_energy_of_poincare p μ hp hR C t ht hP v hv hmed
    have hleft : ∀ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) =
        min (∑ i ∈ Finset.range N, a i x) (threshold n) := by
      intro x
      rw [ENNReal.ofReal_min, hRq]
      change min (vectorEnergy p (v x)) (threshold n) = _
      rw [prefixVector_energy p hp f m N x]
    have hnorm : ∀ s x, vectorEnergy p (v (t s x) - v x) ≤ c s x := by
      intro s x
      rw [vectorEnergy_eq_sum p hp]
      have hb := ENNReal.sum_le_tsum (Finset.range N)
        (f := fun i => ENNReal.ofReal (|f (t s x) i - f x i| ^ p.toReal))
      rw [Finset.sum_range] at hb
      simpa only [scalarEnergy, v, prefixVector, PiLp.sub_apply, PiLp.toLp_apply,
        sub_sub_sub_cancel_right] using hb
    have hr : ∀ s,
        (∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) ≤
          ∫⁻ x, min (c s x) (threshold n) ∂μ := by
      intro s
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ≤
        min (c s x) (threshold n)
      rw [ENNReal.ofReal_min, hRq]
      exact min_le_min_right _ (hnorm s x)
    have hfirst : (∫⁻ x, min (∑ i ∈ Finset.range N, a i x) (threshold n) ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
      simpa only [hleft, K, mul_assoc] using htrunc
    exact hfirst.trans (mul_le_mul_left' (Finset.sum_le_sum fun s _ => hr s) K)
  filter_upwards [hfinite] with x hx
  have hs := ENNReal.summable_toReal hx
  simpa only [a, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)] using hs

end BenchmarkSequencePoincare

#print axioms BenchmarkSequencePoincare.ae_summable_centered_of_poincare
