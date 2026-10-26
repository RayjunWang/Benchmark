import OperatorSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Lean.Elab.Tactic.Omega

/-! Matrix entries of the actual norm-convergent operator coding. -/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def operatorCoordinate (x : HilbertSum H) (i : ℕ) :
    (HilbertSum H →L[ℂ] HilbertSum H) →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 i).comp
    (ContinuousLinearMap.apply ℂ (HilbertSum H) x)

theorem operatorCoordinate_apply (x : HilbertSum H) (i : ℕ)
    (T : HilbertSum H →L[ℂ] HilbertSum H) :
    operatorCoordinate x i T = T x i := rfl

theorem weightedOperator_coordinate (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) (x : HilbertSum H) (i : ℕ) :
    weightedOperator c n A x i = (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) • (A x i) := rfl

theorem starConnector_coordinate (n : ℕ) (x : HilbertSum H) (i : ℕ) :
    starConnector n x i = identityBlock 0 (n + 1) x i + identityBlock (n + 1) 0 x i := rfl

theorem tupleConnector_coordinate (u : ℕ → StrongUnitary H) (n : ℕ) (x : HilbertSum H) (i : ℕ) :
    tupleConnector u n x i =
      blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H) x i +
      blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint x i := rfl

theorem tupleDiagonal_coordinate (x : HilbertSum H) (i : ℕ) :
    tupleDiagonal x i = (((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i : ℝ) : ℂ) • x i := by
  change operatorCoordinate x i tupleDiagonal = _
  rw [tupleDiagonal, (operatorCoordinate x i).map_tsum summable_tupleDiagonal]
  rw [tsum_eq_single i]
  · simp [operatorCoordinate_apply, weightedOperator, identityBlock,
      ContinuousLinearMap.smul_apply, lp.coeFn_smul, blockOperator_coordinate]
  · intro j hji
    simp [operatorCoordinate_apply, weightedOperator, identityBlock,
      ContinuousLinearMap.smul_apply, lp.coeFn_smul, blockOperator_coordinate,
      Ne.symm hji]

theorem tupleDiagonal_single (i : ℕ) (x : H) :
    tupleDiagonal (lp.single 2 i x) =
      lp.single 2 i (((((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i : ℝ) : ℂ)) • x) := by
  apply lp.ext
  funext j
  rw [tupleDiagonal_coordinate]
  by_cases h : j = i
  · subst j
    simp [lp.single_apply]
  · simp [lp.single_apply, h]

theorem tupleImaginaryPart_star_entry (u : ℕ → StrongUnitary H) (j : ℕ) (x : H) :
    tupleImaginaryPart u (lp.single 2 (j + 1) x) 0 =
      ((((1 / 32 : ℝ) * (1 / 2 : ℝ) ^ j : ℝ) : ℂ)) • x := by
  change operatorCoordinate (lp.single 2 (j + 1) x) 0 (tupleImaginaryPart u) = _
  rw [tupleImaginaryPart, map_add,
    (operatorCoordinate _ _).map_tsum summable_starConnectors,
    (operatorCoordinate _ _).map_tsum (summable_tupleConnectors u)]
  have hstar : (∑' n, operatorCoordinate (lp.single 2 (j + 1) x) 0
      (weightedOperator (1 / 32) n (starConnector n))) =
      ((((1 / 32 : ℝ) * (1 / 2 : ℝ) ^ j : ℝ) : ℂ)) • x := by
    rw [tsum_eq_single j]
    · simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply]
    · intro n hnj
      simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, Ne.symm hnj]
  rw [hstar]
  have hzero : (∑' n, operatorCoordinate (lp.single 2 (j + 1) x) 0
      (weightedOperator (1 / 16) n (tupleConnector u n))) = 0 := by
    apply Eq.trans (b := ∑' _ : ℕ, (0 : H))
    · apply tsum_congr
      intro n
      have h₁ : (0 : ℕ) ≠ 2 * n + 1 := by omega
      have h₂ : (0 : ℕ) ≠ 2 * n + 2 := by omega
      simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
        blockOperator_coordinate, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h₁, h₂]
    · simp
  rw [hzero, add_zero]

theorem tupleImaginaryPart_tuple_entry (u : ℕ → StrongUnitary H) (n : ℕ) (x : H) :
    tupleImaginaryPart u (lp.single 2 (2 * n + 2) x) (2 * n + 1) =
      ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)) • u n x := by
  change operatorCoordinate (lp.single 2 (2 * n + 2) x) (2 * n + 1) (tupleImaginaryPart u) = _
  rw [tupleImaginaryPart, map_add,
    (operatorCoordinate _ _).map_tsum summable_starConnectors,
    (operatorCoordinate _ _).map_tsum (summable_tupleConnectors u)]
  have hzero : (∑' k, operatorCoordinate (lp.single 2 (2 * n + 2) x) (2 * n + 1)
      (weightedOperator (1 / 32) k (starConnector k))) = 0 := by
    apply Eq.trans (b := ∑' _ : ℕ, (0 : H))
    · apply tsum_congr
      intro k
      have h₁ : 2 * n + 1 ≠ 0 := by omega
      have h₂ : (0 : ℕ) ≠ 2 * n + 2 := by omega
      simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h₁, h₂]
    · simp
  rw [hzero, zero_add, tsum_eq_single n]
  · have h : 2 * n + 1 ≠ 2 * n + 2 := by omega
    simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
      blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h]
  · intro k hkn
    have h₁ : 2 * n + 1 ≠ 2 * k + 1 := by omega
    have h₂ : 2 * n + 1 ≠ 2 * k + 2 := by omega
    have h₃ : n ≠ k := Ne.symm hkn
    have h₄ : 2 * n ≠ 2 * k + 1 := by omega
    simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
      blockOperator_coordinate, lp.single_apply, h₁, h₂, h₃, h₄]

end OperatorCoding

#print axioms OperatorCoding.tupleDiagonal_coordinate
