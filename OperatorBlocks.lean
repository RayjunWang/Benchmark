import OperatorTargets
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Concrete block operators on a countable Hilbert sum, for the tuple coding.
All blocks are actual bounded operators; the estimates below justify the
operator-norm convergence of the weighted series in the manuscript.
-/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev HilbertSum (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

noncomputable def blockOperator (i j : ℕ) (A : H →L[ℂ] H) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i).comp
    (A.comp (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j))

theorem blockOperator_apply (i j : ℕ) (A : H →L[ℂ] H) (x : HilbertSum H) :
    blockOperator i j A x = lp.single 2 i (A (x j)) := rfl

theorem blockOperator_coordinate (i j k : ℕ) (A : H →L[ℂ] H) (x : HilbertSum H) :
    blockOperator i j A x k = if k = i then A (x j) else 0 := by
  simp [blockOperator_apply, lp.single_apply, Pi.single_apply]

theorem blockOperator_norm_le (i j : ℕ) (A : H →L[ℂ] H) :
    ‖blockOperator i j A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  rw [blockOperator_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact (A.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x j)
      (norm_nonneg A))

theorem blockOperator_single (i j k : ℕ) (A : H →L[ℂ] H) (x : H) :
    blockOperator i j A (lp.single 2 k x) = if j = k then lp.single 2 i (A x) else 0 := by
  by_cases h : j = k
  · subst j
    simp [blockOperator_apply, lp.single_apply]
  · simp [blockOperator_apply, lp.single_apply, Pi.single_apply, h]

theorem blockOperator_same_coordinate (i j : ℕ) (A : H →L[ℂ] H) (x : H) :
    blockOperator i j A (lp.single 2 j x) i = A x := by
  simp [blockOperator_coordinate, lp.single_apply]

theorem blockOperator_add (i j : ℕ) (A B : H →L[ℂ] H) :
    blockOperator i j (A + B) = blockOperator i j A + blockOperator i j B := by
  ext x k
  change blockOperator i j (A + B) x k =
    blockOperator i j A x k + blockOperator i j B x k
  by_cases h : k = i <;> simp [blockOperator_coordinate, h]

theorem blockOperator_smul (i j : ℕ) (c : ℂ) (A : H →L[ℂ] H) :
    blockOperator i j (c • A) = c • blockOperator i j A := by
  ext x k
  by_cases h : k = i <;> simp [blockOperator_coordinate, lp.coeFn_smul, h]

variable [CompleteSpace H]

theorem blockOperator_adjoint (i j : ℕ) (A : H →L[ℂ] H) :
    (blockOperator i j A).adjoint = blockOperator j i A.adjoint := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [blockOperator_apply, blockOperator_apply, lp.inner_single_left, lp.inner_single_right]
  exact A.adjoint_inner_left _ _

end OperatorCoding

#print axioms OperatorCoding.blockOperator_adjoint
