import CantorProbabilityMix
import Mathlib.Analysis.Normed.Module.Convex

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem cantorProbability_convex_neighborhood (μ : ProbabilityMeasure HaarCantor)
    {U : Set (ProbabilityMeasure HaarCantor)} (hU : U ∈ 𝓝 μ) :
    ∃ V : Set (ProbabilityMeasure HaarCantor), IsOpen V ∧ μ ∈ V ∧ V ⊆ U ∧
      ∀ t : unitInterval, ∀ ν ∈ V, ∀ ρ ∈ V, cantorProbabilityMix t ν ρ ∈ V := by
  classical
  obtain ⟨I,W,hW,hWU⟩ := cantorProbability_finite_coordinate_neighborhood μ hU
  choose ε hε hεW using fun k => Metric.mem_nhds_iff.mp (hW k)
  let V : Set (ProbabilityMeasure HaarCantor) :=
    ⋂ k ∈ I, cantorProbabilityCoordinates ⁻¹' {x | x k ∈ Metric.ball (cantorProbabilityCoordinates μ k) (ε k)}
  have hVo : IsOpen V := by
    apply isOpen_biInter_finset
    intro k _hk
    exact Metric.isOpen_ball.preimage ((continuous_apply k).comp continuous_cantorProbabilityCoordinates)
  have hmem (ν : ProbabilityMeasure HaarCantor) : ν ∈ V ↔
      ∀ k ∈ I, cantorProbabilityCoordinates ν k ∈ Metric.ball (cantorProbabilityCoordinates μ k) (ε k) := by
    simp [V]
  refine ⟨V,hVo,(hmem μ).mpr (fun k _ => Metric.mem_ball_self (hε k)), ?_, ?_⟩
  · intro ν hν
    apply hWU
    intro k hk
    exact hεW k ((hmem ν).mp hν k hk)
  · intro t ν hν ρ hρ
    apply (hmem _).mpr
    intro k hk
    change (cantorProbabilityMix t ν ρ : Measure HaarCantor).real (MeasureUnitary.cantorCylinder k) ∈ _
    rw [cantorProbabilityMix_real]
    exact (convex_ball (cantorProbabilityCoordinates μ k) (ε k))
      ((hmem ν).mp hν k hk) ((hmem ρ).mp hρ k hk)
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

end BenchmarkJump

#print axioms BenchmarkJump.cantorProbability_convex_neighborhood
