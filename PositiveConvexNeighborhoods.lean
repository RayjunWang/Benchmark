import PositiveProbabilityMix
import CantorConvexNeighborhoods

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

def PositiveMixConvex (O : Set PositiveCylinderProbabilities) : Prop :=
  ∀ t : unitInterval, ∀ μ ∈ O, ∀ ν ∈ O, positiveProbabilityMix t μ ν ∈ O

theorem positiveProbability_convex_neighborhood (μ : PositiveCylinderProbabilities)
    {U : Set PositiveCylinderProbabilities} (hU : U ∈ 𝓝 μ) :
    ∃ O : Set PositiveCylinderProbabilities,
      IsOpen O ∧ μ ∈ O ∧ O ⊆ U ∧ PositiveMixConvex O := by
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap μ] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨C, hCo, hμC, hCV, hC⟩ := cantorProbability_convex_neighborhood
    (μ : ProbabilityMeasure HaarCantor) hV
  refine ⟨Subtype.val ⁻¹' C, hCo.preimage continuous_subtype_val, hμC,
    fun ν hν => hVU (hCV hν), ?_⟩
  intro t ν hν ρ hρ
  exact hC t ν hν ρ hρ

#print axioms positiveProbability_convex_neighborhood

end BenchmarkJump
