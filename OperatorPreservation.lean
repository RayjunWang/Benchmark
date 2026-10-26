import OperatorAmplification
import OperatorConjugation

/-! A simultaneous conjugacy of the tuple implements a conjugacy of the
single bounded operator by taking its direct sum on all summands. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConjugate_tsum (Q : StrongUnitary H) (f : ℕ → H →L[ℂ] H) :
    Q.conjStarAlgEquiv (∑' n, f n) = ∑' n, Q.conjStarAlgEquiv (f n) := by
  exact Q.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.map_tsum (f := f)

theorem amplifyUnitary_conjugates_block (W : StrongUnitary H) (i j : ℕ)
    (A B : H →L[ℂ] H) (hAB : ∀ x, W (A x) = B (W x)) :
    (amplifyUnitary W).conjStarAlgEquiv (blockOperator i j A) = blockOperator i j B := by
  apply ContinuousLinearMap.ext
  intro x
  simpa using amplifyUnitary_block_intertwines W i j A B hAB ((amplifyUnitary W).symm x)

theorem amplifyUnitary_conjugates_identityBlock (W : StrongUnitary H) (i j : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (identityBlock i j) = identityBlock i j := by
  apply amplifyUnitary_conjugates_block
  intro x
  rfl

theorem amplifyUnitary_conjugates_starConnector (W : StrongUnitary H) (n : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (starConnector n) = starConnector n := by
  simp only [starConnector, map_add, amplifyUnitary_conjugates_identityBlock]

theorem unitary_intertwines_inverse (W U V : StrongUnitary H)
    (h : ∀ x, W (U x) = V (W x)) : ∀ x, W (U.symm x) = V.symm (W x) := by
  intro x
  apply V.injective
  simpa using (h (U.symm x)).symm

theorem amplifyUnitary_conjugates_tupleConnector (W : StrongUnitary H)
    (u v : ℕ → StrongUnitary H) (h : ∀ n x, W (u n x) = v n (W x)) (n : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (tupleConnector u n) = tupleConnector v n := by
  unfold tupleConnector
  rw [map_add]
  congr 1
  · exact amplifyUnitary_conjugates_block W _ _ _ _ (h n)
  · apply amplifyUnitary_conjugates_block
    intro x
    simpa using unitary_intertwines_inverse W (u n) (v n) (h n) x

theorem amplifyUnitary_conjugates_diagonal (W : StrongUnitary H) :
    (amplifyUnitary W).conjStarAlgEquiv tupleDiagonal = tupleDiagonal := by
  unfold tupleDiagonal
  rw [unitaryConjugate_tsum]
  apply tsum_congr
  intro n
  simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_identityBlock]

theorem amplifyUnitary_conjugates_imaginary (W : StrongUnitary H)
    (u v : ℕ → StrongUnitary H) (h : ∀ n x, W (u n x) = v n (W x)) :
    (amplifyUnitary W).conjStarAlgEquiv (tupleImaginaryPart u) = tupleImaginaryPart v := by
  unfold tupleImaginaryPart
  rw [map_add, unitaryConjugate_tsum, unitaryConjugate_tsum]
  congr 1 <;> apply tsum_congr <;> intro n
  · simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_starConnector]
  · simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_tupleConnector W u v h]

theorem tupleCodedOperator_preserves (u v : ℕ → StrongUnitary H)
    (h : TupleConjugate u v) :
    OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v) := by
  obtain ⟨W, hW⟩ := h
  have hw : ∀ n x, W (u n x) = v n (W x) := by
    intro n x
    have hx := congrArg (fun U : StrongUnitary H => U (W x)) (hW n)
    simpa using hx
  apply (operatorUnitaryEquivalent_iff_conjugate _ _).mpr
  refine ⟨amplifyUnitary W, ?_⟩
  simp only [tupleCodedOperator, map_add, map_smul, amplifyUnitary_conjugates_diagonal,
    amplifyUnitary_conjugates_imaginary W u v hw]

end OperatorCoding

#print axioms OperatorCoding.tupleCodedOperator_preserves
