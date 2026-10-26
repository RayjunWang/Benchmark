import ChartConvexNeighborhood

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- Constancy on a comeager part of a nonempty open chart set transfers
to constancy on a comeager part of a nonempty ambient open set. -/
theorem circleChart_local_constancy
    (A : Set CircleSequences) (hAo : IsOpen A)
    (C : Set CircleChartSpace) (hCo : IsOpen C) (hCn : C.Nonempty)
    (hCA : C ⊆ circleChart ⁻¹' A) (P : CircleSequences → Prop)
    (hP : ∀ᶠ x : C in residual C, P (circleChart x)) :
    ∃ O : Set CircleSequences, IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧
      ∀ᶠ y in residual CircleSequences, y ∈ O → P y := by
  classical
  obtain ⟨V, hVo, hVC⟩ := isEmbedding_circleChart.isInducing.isOpen_iff.mp hCo
  let O : Set CircleSequences := V ∩ A
  have hOn : O.Nonempty := by
    obtain ⟨x, hx⟩ := hCn
    exact ⟨circleChart x, by change x ∈ circleChart ⁻¹' V; rw [hVC]; exact hx, hCA hx⟩
  have hm : IsMeagre {x : C | ¬ P (circleChart x)} := by
    simpa only [IsMeagre, compl_setOf, not_not] using hP
  have hImage : IsMeagre
      ((fun x : C => circleChart x) '' {x : C | ¬ P (circleChart x)}) :=
    (isEmbedding_circleChart.isInducing.comp IsInducing.subtypeVal).isMeagre_image hm
  refine ⟨O, hVo.inter hAo, hOn, inter_subset_right, ?_⟩
  filter_upwards [circleChart_range_residual, hImage] with y hyRange hyBad hyO
  obtain ⟨x, rfl⟩ := hyRange
  have hxC : x ∈ C := by
    rw [← hVC]
    exact hyO.1
  by_contra hxP
  exact hyBad ⟨⟨x, hxC⟩, hxP, rfl⟩

theorem boundedDifference_fin_chain (m : ℕ) (u : Fin (m + 1) → RealSequences)
    (hStep : ∀ j : Fin m, BoundedDifference (u j.castSucc) (u j.succ)) :
    BoundedDifference (u 0) (u (Fin.last m)) := by
  have hAux : ∀ j : ℕ, ∀ hj : j ≤ m,
      BoundedDifference (u 0) (u ⟨j, Nat.lt_succ_of_le hj⟩) := by
    intro j
    induction j with
    | zero =>
        intro _hj
        exact boundedDifference_equivalence.refl _
    | succ j ih =>
        intro hj
        have hjm : j < m := by omega
        exact boundedDifference_equivalence.trans (ih (by omega)) (hStep ⟨j, hjm⟩)
  exact hAux m le_rfl

def chainParameter (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) : ℝ := (j : ℝ) / m

theorem chainParameter_nonneg (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) :
    0 ≤ chainParameter m hm j := by unfold chainParameter; positivity

theorem chainParameter_le_one (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) :
    chainParameter m hm j ≤ 1 := by
  unfold chainParameter
  apply (div_le_one (by exact_mod_cast hm)).mpr
  exact_mod_cast Nat.le_of_lt_succ j.isLt

theorem chainParameter_step (m : ℕ) (hm : 0 < m) (j : Fin m) :
    |chainParameter m hm j.castSucc - chainParameter m hm j.succ| = 1 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : chainParameter m hm j.castSucc - chainParameter m hm j.succ = -(1 / (m : ℝ)) := by
    unfold chainParameter
    simp only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]

#print axioms circleChart_local_constancy

end BenchmarkJump
