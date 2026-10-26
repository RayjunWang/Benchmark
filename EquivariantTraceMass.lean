import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic

/-! The Tonelli trace identity behind finite-corner dimension comparison.
It uses actual measurable matrix coefficient masses and an actual
measure-preserving action; no abstract semifinite trace is assumed. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceFiniteCorner

variable {G X : Type*} [Group G] [Countable G] [MeasurableSpace X] [MulAction G X]
    (μ : Measure X) (hmp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)

include hmp in
theorem equivariant_matrix_mass_eq
    (a : G → G → X → ℝ≥0∞) (ha : ∀ d e, Measurable (a d e))
    (hcov : ∀ (g d e : G),
      (fun x => a (g*d) (g*e) (g • x)) =ᵐ[μ] a d e)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hcol : (fun x => ∑' d : G, a d 1 x) =ᵐ[μ] A.indicator (fun _ => 1))
    (hrow : (fun x => ∑' e : G, a 1 e x) =ᵐ[μ] B.indicator (fun _ => 1)) :
    μ A = μ B := by
  have hrow_formula (e : G) : a 1 e =ᵐ[μ] fun x => a e⁻¹ 1 (e⁻¹ • x) := by
    simpa using (hcov e⁻¹ 1 e).symm
  have hentry (e : G) : (∫⁻ x, a 1 e x ∂μ) = ∫⁻ x, a e⁻¹ 1 x ∂μ := by
    rw [lintegral_congr_ae (hrow_formula e)]
    exact (hmp e⁻¹).lintegral_comp (ha _ _)
  calc
    μ A = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by simp [hA]
    _ = ∫⁻ x, ∑' d : G, a d 1 x ∂μ := lintegral_congr_ae hcol.symm
    _ = ∑' d : G, ∫⁻ x, a d 1 x ∂μ := lintegral_tsum (fun d => (ha d 1).aemeasurable)
    _ = ∑' e : G, ∫⁻ x, a e⁻¹ 1 x ∂μ :=
      ((Equiv.inv G).tsum_eq (fun d => ∫⁻ x, a d 1 x ∂μ)).symm
    _ = ∑' e : G, ∫⁻ x, a 1 e x ∂μ := tsum_congr (fun e => (hentry e).symm)
    _ = ∫⁻ x, ∑' e : G, a 1 e x ∂μ :=
      (lintegral_tsum (fun e => (ha 1 e).aemeasurable)).symm
    _ = ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := lintegral_congr_ae hrow
    _ = μ B := by simp [hB]

end MeasureEquivalenceFiniteCorner

#print axioms MeasureEquivalenceFiniteCorner.equivariant_matrix_mass_eq
