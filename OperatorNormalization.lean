import OperatorStrongUnitary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The normalization used before coding a bounded operator by two unitaries.
This file proves the normalization is reversible and exactly preserves
unitary equivalence.  It does not claim the spectral/exponential coding step.
-/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Unitary equivalence on the genuine space of bounded linear operators. -/
def OperatorUnitaryEquivalent (T S : H →L[ℂ] H) : Prop :=
  ∃ u : StrongUnitary H, ∀ x, u (T x) = S (u x)

theorem operatorUnitaryEquivalent_norm {T S : H →L[ℂ] H}
    (h : OperatorUnitaryEquivalent T S) : ‖T‖ = ‖S‖ := by
  obtain ⟨u, hu⟩ := h
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg S)
    intro x
    calc
      ‖T x‖ = ‖u (T x)‖ := (u.norm_map _).symm
      _ = ‖S (u x)‖ := congrArg norm (hu x)
      _ ≤ ‖S‖ * ‖u x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [u.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound S (norm_nonneg T)
    intro x
    obtain ⟨y, rfl⟩ := u.surjective x
    rw [← hu, u.norm_map, u.norm_map]
    exact T.le_opNorm _

noncomputable def normalizeOperator (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (((1 + ‖T‖)⁻¹ : ℝ) : ℂ) • T

theorem norm_normalizeOperator (T : H →L[ℂ] H) :
    ‖normalizeOperator T‖ = ‖T‖ / (1 + ‖T‖) := by
  have h : 0 < 1 + ‖T‖ := by positivity
  rw [normalizeOperator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr h)]
  exact (div_eq_inv_mul _ _).symm

theorem norm_normalizeOperator_lt_one (T : H →L[ℂ] H) :
    ‖normalizeOperator T‖ < 1 := by
  rw [norm_normalizeOperator]
  apply (div_lt_one (by positivity : 0 < 1 + ‖T‖)).mpr
  linarith

theorem recover_normalizeOperator (T : H →L[ℂ] H) :
    ((((1 - ‖normalizeOperator T‖)⁻¹ : ℝ) : ℂ) • normalizeOperator T) = T := by
  have h : (1 + ‖T‖) ≠ 0 := ne_of_gt (by positivity)
  have hc : (1 - ‖T‖ / (1 + ‖T‖))⁻¹ * (1 + ‖T‖)⁻¹ = (1 : ℝ) := by
    field_simp
    <;> ring
  rw [norm_normalizeOperator, normalizeOperator, smul_smul, ← Complex.ofReal_mul,
    hc, Complex.ofReal_one, one_smul]

theorem normalizeOperator_injective :
    Function.Injective (fun T : H →L[ℂ] H => normalizeOperator T) := by
  intro T S h
  dsimp only at h
  calc
    T = ((((1 - ‖normalizeOperator T‖)⁻¹ : ℝ) : ℂ) • normalizeOperator T) :=
      (recover_normalizeOperator T).symm
    _ = ((((1 - ‖normalizeOperator S‖)⁻¹ : ℝ) : ℂ) • normalizeOperator S) := by rw [h]
    _ = S := recover_normalizeOperator S

theorem normalizeOperator_unitaryEquivalent_iff (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent (normalizeOperator T) (normalizeOperator S) ↔
      OperatorUnitaryEquivalent T S := by
  constructor
  · intro h
    have hn := operatorUnitaryEquivalent_norm h
    obtain ⟨u, hu⟩ := h
    refine ⟨u, fun x => ?_⟩
    have hux := congrArg (fun y : H => ((((1 - ‖normalizeOperator T‖)⁻¹ : ℝ) : ℂ) • y)) (hu x)
    dsimp only at hux
    rw [← u.map_smul] at hux
    have ht := congrArg (fun A : H →L[ℂ] H => A x) (recover_normalizeOperator T)
    have hs := congrArg (fun A : H →L[ℂ] H => A (u x)) (recover_normalizeOperator S)
    simp only [ContinuousLinearMap.smul_apply] at ht hs
    rw [ht, hn, hs] at hux
    exact hux
  · intro h
    have hn := operatorUnitaryEquivalent_norm h
    obtain ⟨u, hu⟩ := h
    refine ⟨u, fun x => ?_⟩
    simp only [normalizeOperator, ContinuousLinearMap.smul_apply, u.map_smul, hu, hn]

end OperatorCoding

#print axioms OperatorCoding.normalizeOperator_unitaryEquivalent_iff
