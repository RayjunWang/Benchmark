import OperatorCoefficients
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Self-adjointness and the 7/8 norm bound in the tuple coding. -/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem blockOperator_star (i j : ℕ) (A : H →L[ℂ] H) :
    star (blockOperator i j A) = blockOperator j i (star A) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, blockOperator_adjoint]

theorem identityBlock_star (i j : ℕ) : star (identityBlock (H := H) i j) = identityBlock j i := by
  simp only [identityBlock, ContinuousLinearMap.star_eq_adjoint, blockOperator_adjoint,
    ContinuousLinearMap.adjoint_id]

theorem starConnector_star (n : ℕ) : star (starConnector (H := H) n) = starConnector n := by
  simp [starConnector, star_add, identityBlock_star, add_comm]

theorem tupleConnector_star (u : ℕ → StrongUnitary H) (n : ℕ) :
    star (tupleConnector u n) = tupleConnector u n := by
  simp only [tupleConnector, star_add, ContinuousLinearMap.star_eq_adjoint,
    blockOperator_adjoint, ContinuousLinearMap.adjoint_adjoint, add_comm]

theorem weightedOperator_star (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) :
    star (weightedOperator c n A) = weightedOperator c n (star A) := by
  simp [weightedOperator, star_smul]

theorem tupleDiagonal_star : star (tupleDiagonal (H := H)) = tupleDiagonal := by
  rw [tupleDiagonal, tsum_star]
  congr 1
  funext n
  rw [weightedOperator_star, identityBlock_star]

theorem tupleImaginaryPart_star (u : ℕ → StrongUnitary H) :
    star (tupleImaginaryPart u) = tupleImaginaryPart u := by
  unfold tupleImaginaryPart
  rw [star_add, tsum_star, tsum_star]
  congr 1 <;> congr 1 <;> funext n
  · rw [weightedOperator_star, starConnector_star]
  · rw [weightedOperator_star, tupleConnector_star]

theorem tupleDiagonal_norm_le : ‖tupleDiagonal (H := H)‖ ≤ 1 / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hdom : ‖tupleDiagonal x‖ ≤ ‖((1 / 2 : ℝ) : ℂ) • x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    rw [tupleDiagonal_coordinate]
    change ‖((((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ) • x n)‖ ≤
      ‖(((1 / 2 : ℝ) : ℂ) • x n)‖
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * (1 / 2) ^ n),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hn := norm_nonneg (x n)
    nlinarith
  apply hdom.trans
  rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0), Complex.norm_real]
  norm_num

theorem tupleCodedOperator_norm_le (u : ℕ → StrongUnitary H) :
    ‖tupleCodedOperator u‖ ≤ 7 / 8 := by
  unfold tupleCodedOperator
  apply (norm_add_le (tupleDiagonal (H := H)) (Complex.I • tupleImaginaryPart u)).trans
  have h₁ := tupleDiagonal_norm_le (H := H)
  have h₂ := tupleImaginaryPart_norm_le u
  have h₃ := ContinuousLinearMap.opNorm_smul_le Complex.I (tupleImaginaryPart u)
  norm_num at h₃
  linarith

end OperatorCoding

#print axioms OperatorCoding.tupleCodedOperator_norm_le
#print axioms OperatorCoding.tupleImaginaryPart_star
