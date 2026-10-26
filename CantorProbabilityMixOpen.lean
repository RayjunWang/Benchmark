import CantorProbabilityMixOpenSection

/-! The affine mixture map is open on the full-support Cantor probabilities,
including the two endpoint parameters. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

theorem isOpenMap_positiveProbabilityMix (t : unitInterval) :
    IsOpenMap (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
      positiveProbabilityMix t p.1 p.2) := by
  intro O hO
  apply isOpen_iff_mem_nhds.mpr
  rintro β ⟨⟨μ, ν⟩, hμν, rfl⟩
  let β := positiveProbabilityMix t μ ν
  have hlim : Tendsto (fun n : ℕ => (prefixResample β μ n, prefixResample β ν n))
      atTop (𝓝 (μ, ν)) :=
    (tendsto_prefixResample β μ).prodMk_nhds (tendsto_prefixResample β ν)
  have hOev : ∀ᶠ n : ℕ in atTop, (prefixResample β μ n, prefixResample β ν n) ∈ O :=
    hlim (hO.mem_nhds hμν)
  obtain ⟨n, hn⟩ := hOev.exists
  let R := mixLiftDomain μ ν β n
  let b : R := ⟨β, mixLiftDomain_base μ ν β n⟩
  let L : R → PositiveCylinderProbabilities := mixLiftLeft μ ν β n
  let H : R → PositiveCylinderProbabilities := mixLiftRight μ ν β n
  have hc : Continuous (fun r : R => (L r, H r)) :=
    (continuous_mixLiftLeft μ ν β n).prodMk (continuous_mixLiftRight μ ν β n)
  have hb : (L b, H b) ∈ O := by
    change (mixLiftLeft μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩,
      mixLiftRight μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩) ∈ O
    rwa [mixLiftLeft_base, mixLiftRight_base]
  let N : Set PositiveCylinderProbabilities :=
    (Subtype.val : R → PositiveCylinderProbabilities) '' ((fun r : R => (L r, H r)) ⁻¹' O)
  have hNo : IsOpen N := (isOpen_mixLiftDomain μ ν β n).isOpenMap_subtype_val _ (hO.preimage hc)
  have hbN : β ∈ N := ⟨b, hb, rfl⟩
  apply Filter.mem_of_superset (hNo.mem_nhds hbN)
  intro ρ hρ
  obtain ⟨r, hr, rfl⟩ := hρ
  refine ⟨(L r, H r), hr, ?_⟩
  exact mixLift_exact t μ ν n r

end BenchmarkJump

#print axioms BenchmarkJump.isOpenMap_positiveProbabilityMix
