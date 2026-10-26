import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder

/-! The concrete L2-to-L1 density-square estimate used in the written proof.
This does not define a Hellinger distance or a topology on probability measures.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

noncomputable def square (f : Lp ℝ 2 μ) : Lp ℝ 1 μ := f • f

lemma square_coe (f : Lp ℝ 2 μ) :
    square μ f =ᵐ[μ] fun x => f x ^ 2 := by
  filter_upwards [Lp.coeFn_lpSMul f f (r := 1)] with x hx
  simpa [square, sq, smul_eq_mul] using hx

lemma square_sub_factor (f g : Lp ℝ 2 μ) :
    square μ f - square μ g = ((f - g) • (f + g) : Lp ℝ 1 μ) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (square μ f) (square μ g),
    square_coe μ f, square_coe μ g,
    Lp.coeFn_lpSMul (f - g) (f + g) (r := 1),
    Lp.coeFn_sub f g, Lp.coeFn_add f g] with x hs hf hg hm hd ha
  simp only [Pi.sub_apply, Pi.add_apply, smul_eq_mul, Pi.mul_apply] at *
  rw [hs, hf, hg, hm, hd, ha]
  ring

theorem square_difference_bound (f g : Lp ℝ 2 μ) :
    ‖square μ f - square μ g‖ ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := by
  rw [square_sub_factor]
  exact (Lp.norm_smul_le (r := 1) (f - g) (f + g)).trans
    (mul_le_mul_of_nonneg_left (norm_add_le f g) (norm_nonneg _))

theorem square_continuous : Continuous (square μ) := by
  have h : square μ = fun f : Lp ℝ 2 μ =>
      (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 f f := by
    funext f
    apply Lp.ext
    filter_upwards [square_coe μ f,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) f f] with x h1 h2
    change (square μ f) x =
      ((ContinuousLinearMap.mul ℝ ℝ).holder 1 f f) x
    rw [h1, h2]
    simp [pow_two]
  rw [h]
  exact (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 |>.continuous.clm_apply continuous_id

theorem square_injective_on_nonnegative :
    Set.InjOn (square μ) (Set.Ici (0 : Lp ℝ 2 μ)) := by
  intro f hf g hg hfg
  apply Lp.ext
  have heq : square μ f =ᵐ[μ] square μ g :=
    Filter.Eventually.of_forall (fun x => congrArg (fun h : Lp ℝ 1 μ => h x) hfg)
  filter_upwards [square_coe μ f, square_coe μ g, heq,
    (Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x h1 h2 h3 h4 h5
  have hs : f x ^ 2 = g x ^ 2 := h1.symm.trans (h3.trans h2)
  change 0 ≤ f x at h4
  change 0 ≤ g x at h5
  nlinarith

def positiveUnitSphere : Set (Lp ℝ 2 μ) := {f | 0 ≤ f ∧ ‖f‖ = 1}

theorem positiveUnitSphere_closed : IsClosed (positiveUnitSphere μ) := by
  change IsClosed ({f : Lp ℝ 2 μ | 0 ≤ f} ∩ {f : Lp ℝ 2 μ | ‖f‖ = 1})
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_eq continuous_norm continuous_const)

theorem positiveUnitSphere_complete : CompleteSpace (positiveUnitSphere μ) :=
  (positiveUnitSphere_closed μ).isComplete.completeSpace_coe

end MeasureEquivalenceDensity

#print axioms MeasureEquivalenceDensity.square_difference_bound
#print axioms MeasureEquivalenceDensity.square_continuous
#print axioms MeasureEquivalenceDensity.square_injective_on_nonnegative
#print axioms MeasureEquivalenceDensity.positiveUnitSphere_complete
