import OperatorAdjoints
import Mathlib.Tactic.Module

/-! A unitary conjugacy of coded operators preserves the diagonal marker
and separately intertwines the self-adjoint tuple-coding component. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorUnitaryEquivalent_iff_conjugate (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent T S ↔ ∃ Q : StrongUnitary H, Q.conjStarAlgEquiv T = S := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    ext x
    simpa using hQ (Q.symm x)
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun x => ?_⟩
    have h := congrArg (fun A : H →L[ℂ] H => A (Q x)) hQ
    simpa using h

noncomputable def operatorRealPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (T + star T)

theorem operatorRealPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (operatorRealPart T) = operatorRealPart (Q.conjStarAlgEquiv T) := by
  simp only [operatorRealPart, map_smul, map_add]
  exact congrArg (fun A : H →L[ℂ] H => (1 / 2 : ℂ) • (Q.conjStarAlgEquiv T + A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem tupleCodedOperator_realPart (u : ℕ → StrongUnitary H) :
    operatorRealPart (tupleCodedOperator u) = tupleDiagonal := by
  simp only [operatorRealPart, tupleCodedOperator, star_add, star_smul, tupleDiagonal_star,
    tupleImaginaryPart_star, Complex.star_def, map_neg, Complex.conj_I]
  module

theorem codedOperator_conjugate_diagonal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    Q.conjStarAlgEquiv tupleDiagonal = tupleDiagonal := by
  calc
    Q.conjStarAlgEquiv tupleDiagonal =
        Q.conjStarAlgEquiv (operatorRealPart (tupleCodedOperator u)) := by
      rw [tupleCodedOperator_realPart]
    _ = operatorRealPart (Q.conjStarAlgEquiv (tupleCodedOperator u)) :=
      operatorRealPart_conjugate _ _
    _ = operatorRealPart (tupleCodedOperator v) := by rw [hQ]
    _ = tupleDiagonal := tupleCodedOperator_realPart v

theorem codedOperator_conjugate_imaginary (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    Q.conjStarAlgEquiv (tupleImaginaryPart u) = tupleImaginaryPart v := by
  have hd := codedOperator_conjugate_diagonal u v Q hQ
  have hi : Complex.I • Q.conjStarAlgEquiv (tupleImaginaryPart u) =
      Complex.I • tupleImaginaryPart v := by
    apply add_left_cancel (a := tupleDiagonal)
    simpa only [tupleCodedOperator, map_add, map_smul, hd] using hQ
  exact (smul_right_injective (HilbertSum H →L[ℂ] HilbertSum H)
    (by simp : Complex.I ≠ 0)) hi

theorem codedOperator_commutes_diagonal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x) := by
  intro x
  have h := congrArg (fun T : HilbertSum H →L[ℂ] HilbertSum H => T (Q x))
    (codedOperator_conjugate_diagonal u v Q hQ)
  simpa using h

end OperatorCoding

#print axioms OperatorCoding.codedOperator_conjugate_imaginary
