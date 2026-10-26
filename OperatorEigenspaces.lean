import OperatorAdjoints

/-! The diagonal marker separates all countably many Hilbert summands. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def diagonalEigenvalue (i : ℕ) : ℂ :=
  (((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i : ℝ) : ℂ)

theorem diagonalEigenvalue_injective : Function.Injective diagonalEigenvalue := by
  intro i j h
  have hr : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j :=
    Complex.ofReal_injective h
  have hp : (1 / 2 : ℝ) ^ i = (1 / 2 : ℝ) ^ j :=
    mul_left_cancel₀ (by norm_num : (1 / 2 : ℝ) ≠ 0) hr
  exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≠ 1) hp

theorem tupleDiagonal_eigenvector_support (x : HilbertSum H) (j i : ℕ)
    (hx : tupleDiagonal x = diagonalEigenvalue j • x) (hij : i ≠ j) : x i = 0 := by
  have hcoord := congrArg (fun z : HilbertSum H => z i) hx
  dsimp only at hcoord
  rw [tupleDiagonal_coordinate] at hcoord
  change diagonalEigenvalue i • x i = diagonalEigenvalue j • x i at hcoord
  have hz : (diagonalEigenvalue i - diagonalEigenvalue j) • x i = 0 := by
    rw [sub_smul, hcoord, sub_self]
  have hne : diagonalEigenvalue i - diagonalEigenvalue j ≠ 0 :=
    sub_ne_zero.mpr (fun h => hij (diagonalEigenvalue_injective h))
  exact (smul_eq_zero.mp hz).resolve_left hne

theorem tupleDiagonal_eigenvector_single (x : HilbertSum H) (j : ℕ)
    (hx : tupleDiagonal x = diagonalEigenvalue j • x) : x = lp.single 2 j (x j) := by
  apply lp.ext
  funext i
  by_cases h : i = j
  · subst i
    simp [lp.single_apply]
  · rw [tupleDiagonal_eigenvector_support x j i hx h]
    simp [lp.single_apply, h]

theorem tupleDiagonal_single_eigenvector (j : ℕ) (x : H) :
    tupleDiagonal (lp.single 2 j x) = diagonalEigenvalue j • lp.single 2 j x := by
  rw [tupleDiagonal_single]
  exact lp.single_smul 2 j _ _

noncomputable def diagonalRestriction (Q : StrongUnitary (HilbertSum H)) (j : ℕ) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j).comp
    ((Q : HilbertSum H →L[ℂ] HilbertSum H).comp
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 j))

theorem diagonalRestriction_apply (Q : StrongUnitary (HilbertSum H)) (j : ℕ) (x : H) :
    diagonalRestriction Q j x = Q (lp.single 2 j x) j := rfl

theorem commutingDiagonal_single (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) (x : H) :
    Q (lp.single 2 j x) = lp.single 2 j (diagonalRestriction Q j x) := by
  apply tupleDiagonal_eigenvector_single
  rw [← hQ, tupleDiagonal_single_eigenvector, Q.map_smul]

theorem diagonalRestriction_norm (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) (x : H) :
    ‖diagonalRestriction Q j x‖ = ‖x‖ := by
  have h₁ := lp.norm_single (E := fun _ : ℕ => H) (p := 2)
    (by norm_num) j (diagonalRestriction Q j x)
  have h₂ := lp.norm_single (E := fun _ : ℕ => H) (p := 2) (by norm_num) j x
  calc
    ‖diagonalRestriction Q j x‖ = ‖(lp.single 2 j (diagonalRestriction Q j x) : HilbertSum H)‖ :=
      h₁.symm
    _ = ‖Q (lp.single 2 j x)‖ := congrArg norm (commutingDiagonal_single Q hQ j x).symm
    _ = ‖(lp.single 2 j x : HilbertSum H)‖ := Q.norm_map' (lp.single 2 j x)
    _ = ‖x‖ := h₂

theorem commutingDiagonal_inverse (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) :
    ∀ x, Q.symm (tupleDiagonal x) = tupleDiagonal (Q.symm x) := by
  intro x
  apply Q.injective
  simpa using (hQ (Q.symm x)).symm

theorem diagonalRestriction_surjective (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) :
    Function.Surjective (diagonalRestriction Q j) := by
  intro x
  refine ⟨diagonalRestriction Q.symm j x, ?_⟩
  apply (lp.isometry_single (E := fun _ : ℕ => H) (p := 2) j).injective
  rw [← commutingDiagonal_single Q hQ j]
  rw [← commutingDiagonal_single Q.symm (commutingDiagonal_inverse Q hQ) j]
  exact Q.apply_symm_apply _

noncomputable def diagonalBlockUnitary (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) : StrongUnitary H :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (diagonalRestriction Q j).toLinearMap
      norm_map' := diagonalRestriction_norm Q hQ j }
    (diagonalRestriction_surjective Q hQ j)

theorem diagonalBlockUnitary_apply (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) (x : H) :
    diagonalBlockUnitary Q hQ j x = diagonalRestriction Q j x := rfl

theorem commutingDiagonal_coordinate (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (x : HilbertSum H) (i : ℕ) :
    Q x i = diagonalRestriction Q i (x i) := by
  have hsum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x
  have hcoord := ((hsum.mapL (Q : HilbertSum H →L[ℂ] HilbertSum H)).mapL
    (lp.evalCLM ℂ (fun _ : ℕ => H) 2 i)).tsum_eq
  change (∑' j, Q (lp.single 2 j (x j)) i) = Q x i at hcoord
  rw [← hcoord, tsum_eq_single i]
  · rfl
  · intro j hji
    rw [commutingDiagonal_single Q hQ j]
    simp [lp.single_apply, Ne.symm hji]

end OperatorCoding

#print axioms OperatorCoding.tupleDiagonal_eigenvector_single
#print axioms OperatorCoding.diagonalRestriction_norm
