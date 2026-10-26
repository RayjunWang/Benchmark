import CircleChartConstancy

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- Affine interpolation turns the small-pair bound into generic row
constancy on an actual open cylinder of the product circle chart. -/
theorem circle_interpolation_generic_pairs
    (C : Set CircleChartSpace) (hCo : IsOpen C) (hC : ChartConvex C)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f : CircleSequences → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ circleChart '' C, ∀ z ∈ circleChart '' C,
      y ∈ D → z ∈ D → ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      (∀ i, ‖z i - y i‖ ≤ δ) → BoundedDifference (f y) (f z)) :
    ∀ᶠ p : C × C in residual (C × C),
      BoundedDifference (f (circleChart p.1)) (f (circleChart p.2)) := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  let m : ℕ := M + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdiv : 1 / (m : ℝ) < ε := by exact_mod_cast hM
  let P (j : Fin (m + 1)) : C × C → C := chartMixOn C hC (chainParameter m hm j)
    (chainParameter_nonneg m hm j) (chainParameter_le_one m hm j)
  have hDC : ∀ᶠ x : C in residual C, circleChart x ∈ D :=
    eventually_residual_open_subspace C hCo
      (tendsto_residual_of_denseEmbedding isEmbedding_circleChart denseRange_circleChart hD)
  have hAll : ∀ᶠ p : C × C in residual (C × C),
      ∀ j : Fin (m + 1), circleChart (P j p) ∈ D := by
    apply eventually_countable_forall.mpr
    intro j
    exact tendsto_residual_of_isOpenMap
      (continuous_chartMixOn C hC _ _ _) (isOpenMap_chartMixOn C hCo hC _ _ _) hDC
  filter_upwards [hAll] with p hp
  let u : Fin (m + 1) → RealSequences := fun j => f (circleChart (P j p))
  have hStep (j : Fin m) : BoundedDifference (u j.castSucc) (u j.succ) := by
    apply hSmall (circleChart (P j.castSucc p))
      ⟨P j.castSucc p, (P j.castSucc p).property, rfl⟩
      (circleChart (P j.succ p)) ⟨P j.succ p, (P j.succ p).property, rfl⟩
      (hp j.castSucc) (hp j.succ) (1 / (m : ℝ)) (by positivity) hdiv
    intro i
    have hnorm := circle_affineMix_bound ((p.1 : CircleChartSpace) i : ℝ)
      ((p.2 : CircleChartSpace) i : ℝ)
      (chainParameter m hm j.succ) (chainParameter m hm j.castSucc)
      ⟨((p.1 : CircleChartSpace) i).property.1.le,
        ((p.1 : CircleChartSpace) i).property.2.le⟩
      ⟨((p.2 : CircleChartSpace) i).property.1.le,
        ((p.2 : CircleChartSpace) i).property.2.le⟩
    rw [abs_sub_comm, chainParameter_step m hm j] at hnorm
    exact hnorm
  have hP0 : P 0 p = p.1 := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change affineMix (chainParameter m hm 0)
      (((p.1 : CircleChartSpace) i : ℝ), ((p.2 : CircleChartSpace) i : ℝ)) = _
    simp only [chainParameter, Fin.val_zero, Nat.cast_zero, zero_div, affineMix]
    ring
  have hP1 : P (Fin.last m) p = p.2 := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change affineMix (chainParameter m hm (Fin.last m))
      (((p.1 : CircleChartSpace) i : ℝ), ((p.2 : CircleChartSpace) i : ℝ)) = _
    simp only [chainParameter, Fin.val_last, div_self hm0, affineMix]
    ring
  have hChain := boundedDifference_fin_chain m u hStep
  change BoundedDifference (f (circleChart (P 0 p)))
    (f (circleChart (P (Fin.last m) p))) at hChain
  rwa [hP0, hP1] at hChain

theorem circle_interpolation_constant_on_chart
    (C : Set CircleChartSpace) (hCo : IsOpen C) (hCn : C.Nonempty) (hC : ChartConvex C)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f : CircleSequences → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ circleChart '' C, ∀ z ∈ circleChart '' C,
      y ∈ D → z ∈ D → ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      (∀ i, ‖z i - y i‖ ≤ δ) → BoundedDifference (f y) (f z)) :
    ∃ a : RealSequences, ∀ᶠ x : C in residual C, BoundedDifference (f (circleChart x)) a := by
  letI : PolishSpace CircleChartInterval := isOpen_Ioo.polishSpace
  letI : Nonempty C := hCn.to_subtype
  letI : BaireSpace C := hCo.baireSpace
  have hPair := circle_interpolation_generic_pairs C hCo hC D hD f ε hε hSmall
  obtain ⟨x, hx⟩ := exists_residual_section hPair
  refine ⟨f (circleChart x), ?_⟩
  filter_upwards [hx] with y hy
  exact boundedDifference_equivalence.symm hy

#print axioms circle_interpolation_constant_on_chart

end BenchmarkJump
