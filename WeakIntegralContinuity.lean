import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory Filter Topology

namespace BenchmarkIntegration

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]

theorem integral_dist_le_uniform (μ : ProbabilityMeasure K) (f g : C(K, ℝ)) :
    dist (∫ x, f x ∂(μ : Measure K)) (∫ x, g x ∂(μ : Measure K)) ≤ dist f g := by
  have hf : Integrable f (μ : Measure K) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g (μ : Measure K) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [dist_eq_norm,← integral_sub hf hg,dist_eq_norm]
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure K))
    (f := fun x => f x - g x) (C := ‖f-g‖)
    (Filter.Eventually.of_forall (fun x => (f-g).norm_coe_le_norm x))
  simpa using h

theorem continuous_probability_integral :
    Continuous (fun p : ProbabilityMeasure K × C(K, ℝ) => ∫ x, p.2 x ∂(p.1 : Measure K)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun q : ProbabilityMeasure K × C(K, ℝ) => dist q.2 p.2) (𝓝 p) (𝓝 0) := by
    simpa using (continuous_snd.dist (continuous_const (y := p.2))).tendsto p
  have hc := (ProbabilityMeasure.continuous_integral_continuousMap p.2).comp
    (continuous_fst : Continuous (fun q : ProbabilityMeasure K × C(K, ℝ) => q.1))
  have h₂ : Tendsto (fun q : ProbabilityMeasure K × C(K, ℝ) =>
      dist (∫ x, p.2 x ∂(q.1 : Measure K)) (∫ x, p.2 x ∂(p.1 : Measure K))) (𝓝 p) (𝓝 0) := by
    simpa using (hc.dist (continuous_const (y := ∫ x, p.2 x ∂(p.1 : Measure K)))).tendsto p
  apply squeeze_zero (fun q => dist_nonneg) (fun q => ?_) (by simpa using h₁.add h₂)
  exact (dist_triangle _ (∫ x, p.2 x ∂(q.1 : Measure K)) _).trans
    (add_le_add (integral_dist_le_uniform q.1 q.2 p.2) le_rfl)

end BenchmarkIntegration

#print axioms BenchmarkIntegration.continuous_probability_integral
