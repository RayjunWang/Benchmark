import OperatorPairCoding
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Strong continuity of the operator exponential on uniformly bounded
families. The proof uses continuous powers and the factorial majorant. -/

open Filter Topology ContinuousLinearMap

namespace OperatorCoding

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace α]

theorem strongOperator_continuous_action {A : α → H →L[ℂ] H} {C : ℝ}
    (hA : ∀ v : H, Continuous (fun a => A a v)) (hbound : ∀ a, ‖A a‖ ≤ C)
    {x : α → H} (hx : Continuous x) : Continuous (fun a => A a (x a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun b => C * dist (x b) (x a)) (𝓝 a) (𝓝 0) := by
    simpa using ((continuous_const (y := C)).mul (hx.dist (continuous_const (y := x a)))).tendsto a
  have h₂ : Tendsto (fun b => dist (A b (x a)) (A a (x a))) (𝓝 a) (𝓝 0) := by
    simpa using ((hA (x a)).dist (continuous_const (y := A a (x a)))).tendsto a
  apply squeeze_zero (fun b => dist_nonneg) (fun b => ?_) (by simpa using h₁.add h₂)
  calc
    dist (A b (x b)) (A a (x a)) ≤
        dist (A b (x b)) (A b (x a)) + dist (A b (x a)) (A a (x a)) := dist_triangle _ _ _
    _ ≤ C * dist (x b) (x a) + dist (A b (x a)) (A a (x a)) := by
      exact add_le_add (((A b).dist_le_opNorm (x b) (x a)).trans
        (mul_le_mul_of_nonneg_right (hbound b) dist_nonneg)) le_rfl

theorem strongOperator_pow_continuous {A : α → H →L[ℂ] H} {C : ℝ}
    (hA : ∀ v : H, Continuous (fun a => A a v)) (hbound : ∀ a, ‖A a‖ ≤ C)
    (n : ℕ) (v : H) : Continuous (fun a => ((A a) ^ n) v) := by
  induction n with
  | zero => simpa using (continuous_const (y := v) : Continuous (fun _ : α => v))
  | succ n ih =>
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
      strongOperator_continuous_action hA hbound ih

theorem strongOperator_pow_bound {A : H →L[ℂ] H} {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C)
    (n : ℕ) (v : H) : ‖(A ^ n) v‖ ≤ C ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact (A.le_opNorm _).trans <| calc
      ‖A‖ * ‖(A ^ n) v‖ ≤ C * (C ^ n * ‖v‖) :=
        mul_le_mul hA ih (norm_nonneg _) hC
      _ = C ^ (n + 1) * ‖v‖ := by ring

theorem operatorExp_term_bound {A : H →L[ℂ] H} {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C)
    (n : ℕ) (v : H) :
    ‖((n.factorial : ℂ)⁻¹) • ((A ^ n) v)‖ ≤ ‖v‖ * (C ^ n / n.factorial) := by
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    (n.factorial : ℝ)⁻¹ * ‖(A ^ n) v‖ ≤ (n.factorial : ℝ)⁻¹ * (C ^ n * ‖v‖) :=
      mul_le_mul_of_nonneg_left (strongOperator_pow_bound hC hA n v) (by positivity)
    _ = ‖v‖ * (C ^ n / n.factorial) := by ring

theorem operatorExp_apply_tsum (A : H →L[ℂ] H) (v : H) :
    NormedSpace.exp A v = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • ((A ^ n) v) := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact (ContinuousLinearMap.apply ℂ H v).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)

theorem strongOperator_exp_continuous {A : α → H →L[ℂ] H} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ v : H, Continuous (fun a => A a v)) (hbound : ∀ a, ‖A a‖ ≤ C)
    (v : H) : Continuous (fun a => NormedSpace.exp (A a) v) := by
  have hseries : Continuous (fun a => ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • (((A a) ^ n) v)) := by
    apply continuous_tsum
      (fun n => (strongOperator_pow_continuous hA hbound n v).const_smul ((n.factorial : ℂ)⁻¹))
      ((Real.summable_pow_div_factorial C).mul_left ‖v‖)
    exact fun n a => operatorExp_term_bound hC (hbound a) n v
  simpa only [operatorExp_apply_tsum] using hseries

end OperatorCoding

#print axioms OperatorCoding.strongOperator_exp_continuous
