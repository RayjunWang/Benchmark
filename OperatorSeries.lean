import OperatorBlocks
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The norm-convergent series of the countable unitary-tuple coding. -/

open ContinuousLinearMap

namespace OperatorCoding

set_option maxHeartbeats 1000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def weightedOperator (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) : HilbertSum H →L[ℂ] HilbertSum H :=
  (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) • A

theorem weightedOperator_norm_le {A : ℕ → HilbertSum H →L[ℂ] HilbertSum H}
    {C : ℝ} (hC : ∀ n, ‖A n‖ ≤ C) (c : ℝ) (n : ℕ) :
    ‖weightedOperator c n (A n)‖ ≤ (|c| * C) * (1 / 2 : ℝ) ^ n := by
  calc
    ‖weightedOperator c n (A n)‖ ≤ ‖((c * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)‖ * ‖A n‖ :=
      ContinuousLinearMap.opNorm_smul_le (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) (A n)
    _ = |c| * (1 / 2 : ℝ) ^ n * ‖A n‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ |c| * (1 / 2 : ℝ) ^ n * C := by
      apply mul_le_mul_of_nonneg_left (hC n)
      positivity
    _ = (|c| * C) * (1 / 2 : ℝ) ^ n := by ring

theorem summable_weightedOperator {A : ℕ → HilbertSum H →L[ℂ] HilbertSum H}
    {C : ℝ} (hC : ∀ n, ‖A n‖ ≤ C) (c : ℝ) :
    Summable (fun n => weightedOperator c n (A n)) := by
  exact ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (|c| * C)).of_norm_bounded
      (f := fun n => weightedOperator c n (A n)) (weightedOperator_norm_le hC c)

theorem norm_tsum_weightedOperator_le {A : ℕ → HilbertSum H →L[ℂ] HilbertSum H}
    {C : ℝ} (hC : ∀ n, ‖A n‖ ≤ C) (c : ℝ) :
    ‖∑' n, weightedOperator c n (A n)‖ ≤ 2 * |c| * C := by
  have hg : HasSum (fun n : ℕ => (|c| * C) * (1 / 2 : ℝ) ^ n) (2 * |c| * C) := by
    have hgeo : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := hasSum_geometric_two
    have hscaled := hgeo.mul_left (|c| * C)
    have heq : (|c| * C) * 2 = 2 * |c| * C := by ring
    rw [heq] at hscaled
    exact hscaled
  exact HasSum.norm_le_of_bounded
    (f := fun n => weightedOperator c n (A n))
    (g := fun n => (|c| * C) * (1 / 2 : ℝ) ^ n)
    (summable_weightedOperator hC c).hasSum hg (weightedOperator_norm_le hC c)

noncomputable def identityBlock (i j : ℕ) : HilbertSum H →L[ℂ] HilbertSum H :=
  blockOperator i j (ContinuousLinearMap.id ℂ H)

theorem identityBlock_norm_le (i j : ℕ) : ‖identityBlock (H := H) i j‖ ≤ 1 :=
  (blockOperator_norm_le _ _ _).trans ContinuousLinearMap.norm_id_le

noncomputable def starConnector (n : ℕ) : HilbertSum H →L[ℂ] HilbertSum H :=
  identityBlock 0 (n + 1) + identityBlock (n + 1) 0

theorem starConnector_norm_le (n : ℕ) : ‖starConnector (H := H) n‖ ≤ 2 := by
  unfold starConnector
  exact (norm_add_le (identityBlock (H := H) 0 (n + 1)) (identityBlock (H := H) (n + 1) 0)).trans (by
    have h₁ := identityBlock_norm_le (H := H) 0 (n + 1)
    have h₂ := identityBlock_norm_le (H := H) (n + 1) 0
    linarith)

theorem unitaryCLM_norm_le (u : StrongUnitary H) : ‖(u : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using le_of_eq (u.norm_map x)

noncomputable def tupleConnector (u : ℕ → StrongUnitary H) (n : ℕ) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H) +
  blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint

theorem tupleConnector_norm_le (u : ℕ → StrongUnitary H) (n : ℕ) :
    ‖tupleConnector u n‖ ≤ 2 := by
  unfold tupleConnector
  apply (norm_add_le (blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H))
    (blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint)).trans
  have h₁ := (blockOperator_norm_le (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H)).trans
    (unitaryCLM_norm_le (u n))
  have h₂ : ‖blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint‖ ≤ 1 := by
    apply (blockOperator_norm_le _ _ _).trans
    simpa using unitaryCLM_norm_le (u n).symm
  linarith

noncomputable def tupleDiagonal : HilbertSum H →L[ℂ] HilbertSum H :=
  ∑' n, weightedOperator (1 / 2) n (identityBlock n n)

noncomputable def tupleImaginaryPart (u : ℕ → StrongUnitary H) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  (∑' n, weightedOperator (1 / 32) n (starConnector n)) +
  (∑' n, weightedOperator (1 / 16) n (tupleConnector u n))

noncomputable def tupleCodedOperator (u : ℕ → StrongUnitary H) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  tupleDiagonal + Complex.I • tupleImaginaryPart u

theorem summable_tupleDiagonal :
    Summable (fun n => weightedOperator (H := H) (1 / 2) n (identityBlock n n)) :=
  summable_weightedOperator (fun n => identityBlock_norm_le n n) _

theorem summable_starConnectors :
    Summable (fun n => weightedOperator (H := H) (1 / 32) n (starConnector n)) :=
  summable_weightedOperator starConnector_norm_le _

theorem summable_tupleConnectors (u : ℕ → StrongUnitary H) :
    Summable (fun n => weightedOperator (1 / 16) n (tupleConnector u n)) :=
  summable_weightedOperator (tupleConnector_norm_le u) _

theorem tupleImaginaryPart_norm_le (u : ℕ → StrongUnitary H) :
    ‖tupleImaginaryPart u‖ ≤ 3 / 8 := by
  unfold tupleImaginaryPart
  apply (norm_add_le (∑' n, weightedOperator (H := H) (1 / 32) n (starConnector n))
    (∑' n, weightedOperator (1 / 16) n (tupleConnector u n))).trans
  have h₁ := norm_tsum_weightedOperator_le (H := H) starConnector_norm_le (1 / 32)
  have h₂ := norm_tsum_weightedOperator_le (tupleConnector_norm_le u) (1 / 16)
  norm_num at h₁ h₂
  linarith

end OperatorCoding

#print axioms OperatorCoding.tupleImaginaryPart_norm_le
