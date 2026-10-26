import RadialEnergy

/-! Applying a scalar median Poincaré bound to radial truncations. Strict
positivity of the radial multiplier preserves the positive and negative
sets of every coordinate, so the medians remain zero. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkPoincareRadial

variable {X S I : Type*} [MeasurableSpace X] [Fintype S] [Fintype I]

def ZeroMedian (μ : Measure X) (f : X → ℝ) : Prop :=
  μ {x | f x < 0} ≤ μ univ / 2 ∧ μ {x | 0 < f x} ≤ μ univ / 2

def ScalarPoincareBound (p : ℝ≥0∞) (μ : Measure X) (t : S → X → X) (C : ℝ≥0∞) : Prop :=
  ∀ f : X → ℝ, Measurable f → ZeroMedian μ f →
    (∃ B : ℝ, ∀ x, |f x| ≤ B) →
    (∫⁻ x, BenchmarkRadialEnergy.scalarEnergy p (f x) ∂μ) ≤
      C * ∑ s : S, ∫⁻ x, BenchmarkRadialEnergy.scalarEnergy p (f (t s x) - f x) ∂μ

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X)

theorem zeroMedian_radial_coordinate {R : ℝ} (hR : 0 < R)
    (v : X → BenchmarkRadialEnergy.Vector (I := I) p) (i : I)
    (hm : ZeroMedian μ (fun x => v x i)) :
    ZeroMedian μ (fun x => BenchmarkRadial.radial R (v x) i) := by
  have hc : ∀ x, 0 < R / max R ‖v x‖ := fun x =>
    div_pos hR (lt_of_lt_of_le hR (le_max_left _ _))
  have hneg : {x | BenchmarkRadial.radial R (v x) i < 0} = {x | v x i < 0} := by
    ext x
    simp only [mem_setOf_eq, BenchmarkRadial.radial, PiLp.smul_apply, smul_eq_mul]
    constructor
    · intro h
      by_contra hb
      have hb0 : 0 ≤ v x i := le_of_not_gt hb
      have hh := mul_nonneg (hc x).le hb0
      linarith
    · intro h
      have hh := mul_pos (hc x) (neg_pos.mpr h)
      nlinarith
  have hpos : {x | 0 < BenchmarkRadial.radial R (v x) i} = {x | 0 < v x i} := by
    ext x
    simp only [mem_setOf_eq, BenchmarkRadial.radial, PiLp.smul_apply, smul_eq_mul]
    exact mul_pos_iff_of_pos_left (hc x)
  unfold ZeroMedian at hm ⊢
  rwa [hneg, hpos]

theorem truncated_energy_of_poincare
    (hp : p ≠ ∞) {R : ℝ} (hR : 0 < R) (C : ℝ≥0∞)
    (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hP : ScalarPoincareBound p μ t C)
    (v : X → BenchmarkRadialEnergy.Vector (I := I) p) (hv : Measurable v)
    (hm : ∀ i, ZeroMedian μ (fun x => v x i)) :
    (∫⁻ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p.toReal) * C *
        ∑ s : S, ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
  apply BenchmarkRadialEnergy.truncated_energy_from_scalar p μ hp hR C t ht v hv
  intro i
  apply hP
  · exact (PiLp.continuous_apply p (β := fun _ : I => ℝ) i).measurable.comp
      ((BenchmarkRadialEnergy.continuous_radial hR).measurable.comp hv)
  · exact zeroMedian_radial_coordinate p μ hR v i (hm i)
  · refine ⟨R, fun x => ?_⟩
    have hb := (PiLp.norm_apply_le (p := p) (BenchmarkRadial.radial R (v x)) i).trans
      (BenchmarkRadial.norm_radial_le hR (v x))
    simpa only [Real.norm_eq_abs] using hb

end BenchmarkPoincareRadial

#print axioms BenchmarkPoincareRadial.truncated_energy_of_poincare
