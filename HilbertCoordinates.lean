import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-! Countable real coordinates for a separable real Hilbert space, preserving
the squared norm as an actual summable series. No infinite-dimensionality
assumption is used: unused natural-number coordinates are zero.
-/

open Set Filter TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

namespace MeasureEquivalenceHilbertCoordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma orthonormal_index_countable [SeparableSpace H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal ℝ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 3 : ℝ))
      (Metric.ball (v j) (1 / 3 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hn : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

theorem exists_continuous_coordinates [CompleteSpace H] [SeparableSpace H] :
    ∃ F : H → (ℕ → ℝ), Continuous F ∧ ∀ x y : H,
      HasSum (fun n => (F x n - F y n) ^ 2) (‖x - y‖ ^ 2) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ H
  have : Countable w := orthonormal_index_countable b.orthonormal
  obtain ⟨e, he⟩ := exists_injective_nat w
  let F : H → (ℕ → ℝ) := fun x => Function.extend e (fun i => inner ℝ (b i) x) 0
  refine ⟨F, ?_, ?_⟩
  · apply continuous_pi
    intro n
    by_cases hn : n ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hn
      have hF : (fun x => F x (e i)) = (fun x => inner ℝ (b i) x) := by
        funext x
        exact he.extend_apply _ _ i
      rw [hF]
      fun_prop
    · have hF : (fun x => F x n) = (fun _ : H => (0 : ℝ)) := by
        funext x
        exact Function.extend_apply' _ _ _ hn
      rw [hF]
      exact continuous_const
  · intro x y
    have hb : HasSum (fun i => (inner ℝ (b i) x - inner ℝ (b i) y) ^ 2)
        (‖x - y‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
        b.repr_apply_apply, inner_sub_right, b.repr.norm_map] using
        lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr (x - y))
    have hF : (fun n => (F x n - F y n) ^ 2) =
        Function.extend e (fun i => (inner ℝ (b i) x - inner ℝ (b i) y) ^ 2) 0 := by
      funext n
      by_cases hn : n ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hn
        simp only [F, he.extend_apply]
      · simp only [F, Function.extend_apply' _ _ _ hn, Pi.zero_apply, sub_self]
        norm_num
    rw [hF]
    exact (hasSum_extend_zero he).2 hb

#print axioms exists_continuous_coordinates

end MeasureEquivalenceHilbertCoordinates
