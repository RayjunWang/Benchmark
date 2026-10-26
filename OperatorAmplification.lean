import OperatorAdjoints

/-! The direct sum of one unitary on every Hilbert summand. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def amplifyUnitary (W : StrongUnitary H) : StrongUnitary (HilbertSum H) where
  toLinearEquiv :=
    { toFun := fun x => ⟨fun i => W (x i), by
        apply Memℓp.of_norm
        simpa only [W.norm_map] using x.property.norm⟩
      invFun := fun x => ⟨fun i => W.symm (x i), by
        apply Memℓp.of_norm
        simpa only [W.symm.norm_map] using x.property.norm⟩
      left_inv := by
        intro x
        apply lp.ext
        funext i
        exact W.symm_apply_apply (x i)
      right_inv := by
        intro x
        apply lp.ext
        funext i
        exact W.apply_symm_apply (x i)
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        exact W.map_add (x i) (y i)
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        exact W.map_smul c (x i) }
  norm_map' := by
    intro x
    apply le_antisymm
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      exact le_of_eq (W.norm_map (x i))
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      exact le_of_eq (W.norm_map (x i)).symm

theorem amplifyUnitary_apply (W : StrongUnitary H) (x : HilbertSum H) (i : ℕ) :
    amplifyUnitary W x i = W (x i) := rfl

theorem amplifyUnitary_single (W : StrongUnitary H) (i : ℕ) (x : H) :
    amplifyUnitary W (lp.single 2 i x) = lp.single 2 i (W x) := by
  apply lp.ext
  funext j
  by_cases h : j = i
  · subst j
    simp [amplifyUnitary_apply, lp.single_apply]
  · simp [amplifyUnitary_apply, lp.single_apply, h]

theorem amplifyUnitary_block_intertwines (W : StrongUnitary H) (i j : ℕ)
    (A B : H →L[ℂ] H) (hAB : ∀ x, W (A x) = B (W x)) (x : HilbertSum H) :
    amplifyUnitary W (blockOperator i j A x) = blockOperator i j B (amplifyUnitary W x) := by
  apply lp.ext
  funext k
  by_cases h : k = i
  · subst k
    simp [amplifyUnitary_apply, blockOperator_coordinate, hAB]
  · simp [amplifyUnitary_apply, blockOperator_coordinate, h]

end OperatorCoding

#print axioms OperatorCoding.amplifyUnitary
