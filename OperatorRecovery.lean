import OperatorEigenspaces
import OperatorConjugation

/-! Recovery of one simultaneous intertwiner from a conjugacy of the coded
bounded operators.  The star-shaped identity edges force all diagonal
unitaries to coincide, and the remaining edges recover every input unitary. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveGeometric_coefficient_ne_zero (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero hc (pow_ne_zero _ (by norm_num))

theorem conjugate_eq_intertwines (Q : StrongUnitary H) (T S : H →L[ℂ] H)
    (h : Q.conjStarAlgEquiv T = S) : ∀ x, Q (T x) = S (Q x) := by
  intro x
  have hx := congrArg (fun A : H →L[ℂ] H => A (Q x)) h
  simpa using hx

theorem coding_diagonalRestrictions_equal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hd : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x))
    (hb : ∀ x, Q (tupleImaginaryPart u x) = tupleImaginaryPart v (Q x))
    (j : ℕ) (x : H) : diagonalRestriction Q j x = diagonalRestriction Q 0 x := by
  cases j with
  | zero => rfl
  | succ j =>
    have h := congrArg (fun z : HilbertSum H => z 0) (hb (lp.single 2 (j + 1) x))
    dsimp only at h
    rw [commutingDiagonal_coordinate Q hd, tupleImaginaryPart_star_entry,
      commutingDiagonal_single Q hd, tupleImaginaryPart_star_entry,
      (diagonalRestriction Q 0).map_smul] at h
    exact ((smul_right_injective H
      (positiveGeometric_coefficient_ne_zero (1 / 32) (by norm_num) j)) h).symm

theorem coding_recovered_intertwiner (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hd : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x))
    (hb : ∀ x, Q (tupleImaginaryPart u x) = tupleImaginaryPart v (Q x))
    (n : ℕ) (x : H) :
    diagonalRestriction Q 0 (u n x) = v n (diagonalRestriction Q 0 x) := by
  have h := congrArg (fun z : HilbertSum H => z (2 * n + 1))
    (hb (lp.single 2 (2 * n + 2) x))
  dsimp only at h
  rw [commutingDiagonal_coordinate Q hd, tupleImaginaryPart_tuple_entry,
    commutingDiagonal_single Q hd, tupleImaginaryPart_tuple_entry,
    (diagonalRestriction Q (2 * n + 1)).map_smul] at h
  rw [coding_diagonalRestrictions_equal u v Q hd hb (2 * n + 1),
    coding_diagonalRestrictions_equal u v Q hd hb (2 * n + 2)] at h
  exact (smul_right_injective H
    (positiveGeometric_coefficient_ne_zero (1 / 16) (by norm_num) n)) h

theorem tupleCodedOperator_reflects (u v : ℕ → StrongUnitary H)
    (h : OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v)) :
    TupleConjugate u v := by
  obtain ⟨Q, hQ⟩ := (operatorUnitaryEquivalent_iff_conjugate _ _).mp h
  have hd := codedOperator_commutes_diagonal u v Q hQ
  have hb := conjugate_eq_intertwines Q _ _ (codedOperator_conjugate_imaginary u v Q hQ)
  let W := diagonalBlockUnitary Q hd 0
  refine ⟨W, fun n => ?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  have hx := coding_recovered_intertwiner u v Q hd hb n (W.symm x)
  change W (u n (W.symm x)) = v n (W (W.symm x)) at hx
  simpa using hx

end OperatorCoding

#print axioms OperatorCoding.tupleCodedOperator_reflects
