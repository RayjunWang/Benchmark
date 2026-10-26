import CantorHaarCoordinates

open Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

/-- On the unit sphere of real ℓ², continuous coordinates imply norm
continuity. The proof uses finite-coordinate approximation and Cauchy--Schwarz. -/
theorem continuous_haarCoefficients_of_unit_coordinates {X : Type*} [TopologicalSpace X]
    (F : X → HaarCoefficientSpace) (hNorm : ∀ x, ‖F x‖ = 1)
    (hCoord : ∀ i : Option HaarNodeIndex, Continuous (fun x => F x i)) : Continuous F := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε ^ 2 / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc (F x₀)) δ hδ).exists
  let b : HaarCoefficientSpace := haarCoefficientTrunc s (F x₀)
  have hb : ‖F x₀ - b‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hs
  have hFinite : Continuous (fun x => inner ℝ (F x) b) := by
    change Continuous (fun x => inner ℝ (F x)
      (∑ i ∈ s, lp.single 2 i (F x₀ i)))
    simp only [inner_sum, lp.inner_single_right]
    apply continuous_finsetSum
    intro i _hi
    exact (hCoord i).inner continuous_const
  have hNear := Metric.tendsto_nhds.mp (hFinite.tendsto x₀) δ hδ
  filter_upwards [hNear] with x hx
  have hTailX : |inner ℝ (F x) (F x₀) - inner ℝ (F x) b| ≤ ‖F x₀ - b‖ := by
    rw [← inner_sub_right]
    simpa only [Real.norm_eq_abs, hNorm, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (F x) (F x₀ - b)
  have hTail₀ : |inner ℝ (F x₀) (F x₀) - inner ℝ (F x₀) b| ≤ ‖F x₀ - b‖ := by
    rw [← inner_sub_right]
    simpa only [Real.norm_eq_abs, hNorm, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (F x₀) (F x₀ - b)
  have hSelf : inner ℝ (F x₀) (F x₀) = 1 := by
    rw [real_inner_self_eq_norm_sq, hNorm]
    norm_num
  rw [hSelf] at hTail₀
  have hN := norm_sub_sq_real (F x) (F x₀)
  rw [hNorm, hNorm] at hN
  have hxAbs : |inner ℝ (F x) b - inner ℝ (F x₀) b| < δ := hx
  have hSq : ‖F x - F x₀‖ ^ 2 < ε ^ 2 := by
    have h1 := (abs_le.mp hTailX).1
    have h2 := (abs_le.mp hTail₀).2
    have h3 := (abs_lt.mp hxAbs).1
    dsimp [δ] at hb hxAbs h3
    nlinarith
  simpa only [dist_eq_norm] using (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hSq

#print axioms continuous_haarCoefficients_of_unit_coordinates

end BenchmarkJump
