import ContinuousSquareReweight
import PositiveConvexNeighborhoods

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem continuousSquareReweightHomeomorph_apply (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) :
    continuousSquareReweightHomeomorph w hw μ = continuousSquareReweight w hw μ := rfl

theorem homeomorph_positive_convex_neighborhood
    (H : PositiveCylinderProbabilities ≃ₜ PositiveCylinderProbabilities)
    (U A : Set PositiveCylinderProbabilities) (hUo : IsOpen U) (hAo : IsOpen A)
    (μ₀ : PositiveCylinderProbabilities) (hμ₀U : μ₀ ∈ U) (hHμ₀A : H μ₀ ∈ A) :
    ∃ O : Set PositiveCylinderProbabilities,
      IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧ PositiveMixConvex O ∧
      ∀ σ ∈ O, ∃ ρ ∈ U, H ρ = σ := by
  let N : Set PositiveCylinderProbabilities := A ∩ H.symm ⁻¹' U
  have hNo : IsOpen N := hAo.inter (hUo.preimage H.symm.continuous)
  have hHμ₀N : H μ₀ ∈ N := by
    refine ⟨hHμ₀A, ?_⟩
    change H.symm (H μ₀) ∈ U
    simpa only [H.symm_apply_apply] using hμ₀U
  obtain ⟨O, hOo, hHO, hON, hConvex⟩ :=
    positiveProbability_convex_neighborhood (H μ₀) (hNo.mem_nhds hHμ₀N)
  refine ⟨O, hOo, ⟨H μ₀, hHO⟩, fun σ hσ => (hON hσ).1, hConvex, ?_⟩
  intro σ hσ
  exact ⟨H.symm σ, (hON hσ).2, H.apply_symm_apply σ⟩

theorem positiveReweight_convex_neighborhood
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (U A : Set PositiveCylinderProbabilities) (hUo : IsOpen U) (hAo : IsOpen A)
    (μ₀ : PositiveCylinderProbabilities) (hμ₀U : μ₀ ∈ U)
    (hHμ₀A : continuousSquareReweight w hw μ₀ ∈ A) :
    ∃ O : Set PositiveCylinderProbabilities,
      IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧ PositiveMixConvex O ∧
      ∀ σ ∈ O, ∃ ρ ∈ U, continuousSquareReweight w hw ρ = σ := by
  have h := homeomorph_positive_convex_neighborhood (continuousSquareReweightHomeomorph w hw)
    U A hUo hAo μ₀ hμ₀U (by rwa [continuousSquareReweightHomeomorph_apply])
  simpa only [continuousSquareReweightHomeomorph_apply] using h

#print axioms positiveReweight_convex_neighborhood

end BenchmarkJump
