import OperatorRecovery
import OperatorPreservation
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
The manuscript's explicit continuous reduction from simultaneous unitary
equivalence of countable tuples to unitary equivalence of a single operator.
The target is the actual countable Hilbert sum, with the strong operator
topology, and the resulting operators have norm at most 7/8.
-/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tupleConnector_continuous_apply (n : ℕ) (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleConnector u n x) := by
  have h₁ : Continuous (fun u : ℕ → StrongUnitary H => u n (x (2 * n + 2))) :=
    (strongUnitary_continuous_eval _).comp (continuous_apply n)
  have h₂ : Continuous (fun u : ℕ → StrongUnitary H => (u n).symm (x (2 * n + 1))) :=
    (strongUnitary_continuous_eval _).comp (continuous_apply n).inv
  have hs₁ := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 (2 * n + 1)).continuous.comp h₁
  have hs₂ := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 (2 * n + 2)).continuous.comp h₂
  simpa only [tupleConnector, ContinuousLinearMap.add_apply, blockOperator_apply,
    LinearIsometryEquiv.adjoint_eq_symm, lp.singleContinuousLinearMap_apply] using hs₁.add hs₂

theorem weightedTupleConnector_continuous_apply (n : ℕ) (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => weightedOperator (1 / 16) n (tupleConnector u n) x) := by
  exact (tupleConnector_continuous_apply n x).const_smul
    ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ))

theorem weightedTupleConnector_norm_bound (n : ℕ) (u : ℕ → StrongUnitary H) (x : HilbertSum H) :
    ‖weightedOperator (1 / 16) n (tupleConnector u n) x‖ ≤
      (‖x‖ / 8) * (1 / 2 : ℝ) ^ n := by
  have hb := weightedOperator_norm_le (tupleConnector_norm_le u) (1 / 16) n
  norm_num at hb
  calc
    ‖weightedOperator (1 / 16) n (tupleConnector u n) x‖ ≤
        ‖weightedOperator (1 / 16) n (tupleConnector u n)‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    _ = (‖x‖ / 8) * (1 / 2 : ℝ) ^ n := by ring

theorem tupleImaginaryPart_continuous_apply (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleImaginaryPart u x) := by
  have hsum : Continuous (fun u : ℕ → StrongUnitary H =>
      ∑' n, weightedOperator (1 / 16) n (tupleConnector u n) x) := by
    apply continuous_tsum (fun n => weightedTupleConnector_continuous_apply n x)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (‖x‖ / 8))
    exact fun n u => weightedTupleConnector_norm_bound n u x
  have hconst : Continuous (fun _ : ℕ → StrongUnitary H =>
    (∑' n, weightedOperator (H := H) (1 / 32) n (starConnector n)) x) := continuous_const
  convert hconst.add hsum using 1
  funext u
  rw [tupleImaginaryPart, ContinuousLinearMap.add_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ (HilbertSum H) x).map_tsum (summable_tupleConnectors u)

theorem tupleCodedOperator_continuous_apply (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleCodedOperator u x) := by
  exact continuous_const.add ((tupleImaginaryPart_continuous_apply x).const_smul Complex.I)

/-- The strong topology on the space containing the coded operators. -/
noncomputable abbrev hilbertSumOperatorStrongTopology :
    TopologicalSpace (HilbertSum H →L[ℂ] HilbertSum H) :=
  TopologicalSpace.induced
    (fun T : HilbertSum H →L[ℂ] HilbertSum H => fun x : HilbertSum H => T x) inferInstance

theorem tupleCodedOperator_continuous :
    @Continuous (ℕ → StrongUnitary H) (HilbertSum H →L[ℂ] HilbertSum H)
      inferInstance hilbertSumOperatorStrongTopology tupleCodedOperator := by
  apply continuous_induced_rng.mpr
  exact continuous_pi tupleCodedOperator_continuous_apply

theorem tupleCodedOperator_equivalent_iff (u v : ℕ → StrongUnitary H) :
    OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v) ↔
      TupleConjugate u v :=
  ⟨tupleCodedOperator_reflects u v, tupleCodedOperator_preserves u v⟩

/-- The full explicit coding lemma, with its continuity, norm bound and exact
preservation and reflection of equivalence all checked together. -/
theorem countable_unitary_tuple_coding :
    ∃ f : (ℕ → StrongUnitary H) → (HilbertSum H →L[ℂ] HilbertSum H),
      @Continuous _ _ inferInstance hilbertSumOperatorStrongTopology f ∧
      (∀ u, ‖f u‖ ≤ 7 / 8) ∧
      ∀ u v, OperatorUnitaryEquivalent (f u) (f v) ↔ TupleConjugate u v := by
  exact ⟨tupleCodedOperator, tupleCodedOperator_continuous,
    tupleCodedOperator_norm_le, tupleCodedOperator_equivalent_iff⟩

end OperatorCoding

#print axioms OperatorCoding.countable_unitary_tuple_coding
