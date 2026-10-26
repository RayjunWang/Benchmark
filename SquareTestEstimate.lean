import DensityMeasure
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace BenchmarkIntegration

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]

theorem square_test_difference_bound (μ : Measure K) (f g : Lp ℝ 2 μ) (h : C(K, ℝ)) :
    |(∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ f : Measure K)) -
      (∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ g : Measure K))| ≤
      ‖h‖ * ‖f - g‖ * (‖f‖ + ‖g‖) := by
  let k := MeasureEquivalenceDensity.square μ f - MeasureEquivalenceDensity.square μ g
  have hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ ‖h‖ := Eventually.of_forall h.norm_coe_le_norm
  have hf := (MeasureEquivalenceDensity.integrable_square μ f).mul_bdd
    h.continuous.aestronglyMeasurable hb
  have hg := (MeasureEquivalenceDensity.integrable_square μ g).mul_bdd
    h.continuous.aestronglyMeasurable hb
  have hk : k =ᵐ[μ] (fun x => f x ^ 2 - g x ^ 2) := by
    filter_upwards [Lp.coeFn_sub (MeasureEquivalenceDensity.square μ f)
      (MeasureEquivalenceDensity.square μ g),
      MeasureEquivalenceDensity.square_coe μ f,
      MeasureEquivalenceDensity.square_coe μ g] with x hs h1 h2
    change k x = _
    simp only [Pi.sub_apply] at hs
    rw [show k x = _ from hs, h1, h2]
  have he : (∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ f : Measure K)) -
      (∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ g : Measure K)) =
      ∫ x, h x * k x ∂μ := by
    rw [MeasureEquivalenceDensity.squareMeasure_integral,
      MeasureEquivalenceDensity.squareMeasure_integral, ← integral_sub hf hg]
    apply integral_congr_ae
    filter_upwards [hk] with x hx
    rw [hx]
    ring
  rw [he, ← Real.norm_eq_abs]
  have hi := norm_integral_le_of_norm_le (f := fun x : K => h x * k x)
    ((L1.integrable_coeFn k).norm.const_mul ‖h‖)
    (Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm x) (norm_nonneg (k x))))
  have hi' : ‖∫ x, h x * k x ∂μ‖ ≤ ‖h‖ * ‖k‖ := by
    simpa only [integral_const_mul, ← L1.norm_eq_integral_norm] using hi
  calc
    _ ≤ ‖h‖ * ‖k‖ := hi'
    _ ≤ ‖h‖ * (‖f - g‖ * (‖f‖ + ‖g‖)) :=
      mul_le_mul_of_nonneg_left (MeasureEquivalenceDensity.square_difference_bound μ f g) (norm_nonneg _)
    _ = _ := by ring

end BenchmarkIntegration

#print axioms BenchmarkIntegration.square_test_difference_bound
