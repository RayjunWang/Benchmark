import DensitySquare
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Concrete finite measures with an L2 square density. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

lemma integrable_square (f : Lp ℝ 2 μ) : Integrable (fun x => f x ^ 2) μ :=
  (L1.integrable_coeFn (square μ f)).congr (square_coe μ f)

noncomputable def squareMeasure (f : Lp ℝ 2 μ) : FiniteMeasure α :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)),
    isFiniteMeasure_withDensity_ofReal (integrable_square μ f).hasFiniteIntegral⟩

theorem squareMeasure_ac (f : Lp ℝ 2 μ) :
    (squareMeasure μ f : Measure α) ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem squareMeasure_injective_nonnegative [SigmaFinite μ] :
    Set.InjOn (squareMeasure μ) (Set.Ici (0 : Lp ℝ 2 μ)) := by
  intro f hf g hg hfg
  have heq : μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)) =
      μ.withDensity (fun x => ENNReal.ofReal (g x ^ 2)) :=
    congrArg (fun ν : FiniteMeasure α => (ν : Measure α)) hfg
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((Lp.aestronglyMeasurable f).aemeasurable.pow_const 2).ennreal_ofReal
    ((Lp.aestronglyMeasurable g).aemeasurable.pow_const 2).ennreal_ofReal).mp heq
  apply Lp.ext
  filter_upwards [hae, (Lp.coeFn_nonneg f).mpr hf,
    (Lp.coeFn_nonneg g).mpr hg] with x h1 h2 h3
  change 0 ≤ f x at h2
  change 0 ≤ g x at h3
  have hs := congrArg ENNReal.toReal h1
  simp only [ENNReal.toReal_ofReal (sq_nonneg (f x)),
    ENNReal.toReal_ofReal (sq_nonneg (g x))] at hs
  nlinarith

theorem squareMeasure_integral (f : Lp ℝ 2 μ) (g : α → ℝ) :
    ∫ x, g x ∂(squareMeasure μ f : Measure α) = ∫ x, f x ^ 2 * g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable f).aemeasurable.pow_const 2).ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp [ENNReal.toReal_ofReal, sq_nonneg, smul_eq_mul]

theorem squareMeasure_continuous [TopologicalSpace α] [BorelSpace α] :
    Continuous (squareMeasure μ) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro g
  let gLp : Lp ℝ ∞ μ := (g.memLp_top (μ := μ)).toLp g
  let B : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 1 1
  have hEq : (fun f : Lp ℝ 2 μ => ∫ x, g x ∂(squareMeasure μ f : Measure α)) =
      fun f => ∫ x, (B gLp (square μ f)) x ∂μ := by
    funext f
    rw [squareMeasure_integral]
    apply integral_congr_ae
    filter_upwards [square_coe μ f, (g.memLp_top (μ := μ)).coeFn_toLp,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) gLp (square μ f)]
      with x h1 h2 h3
    change f x ^ 2 * g x = ((ContinuousLinearMap.mul ℝ ℝ).holder 1 gLp (square μ f)) x
    rw [h3]
    change f x ^ 2 * g x = gLp x * (square μ f) x
    change gLp x = g x at h2
    rw [h1, h2, mul_comm]
  rw [hEq]
  exact continuous_integral.comp ((B gLp).continuous.comp (square_continuous μ))

end MeasureEquivalenceDensity

#print axioms MeasureEquivalenceDensity.squareMeasure_ac
#print axioms MeasureEquivalenceDensity.squareMeasure_injective_nonnegative
#print axioms MeasureEquivalenceDensity.squareMeasure_integral
#print axioms MeasureEquivalenceDensity.squareMeasure_continuous
