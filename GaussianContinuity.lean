import GaussianCriterion
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The actual Gaussian family is continuous for the product topology on real sequences
and the weak topology on probability measures. Together with GaussianCriterion this
is a continuous reduction of square-summable difference to mutual absolute continuity.
-/

open MeasureTheory ProbabilityTheory Filter Set BoundedContinuousFunction
open scoped ENNReal BigOperators Topology

namespace MeasureEquivalenceGaussian

noncomputable def gaussianProbability (a : ℕ → ℝ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨gaussianProduct a, inferInstance⟩

lemma gaussianProduct_map_add (a b : ℕ → ℝ) :
    (gaussianProduct b).map (fun x => x + a) = gaussianProduct (b + a) := by
  unfold gaussianProduct
  convert Measure.infinitePi_map_pi (fun n => gaussianReal (b n) 1)
    (f := fun i x => x + a i) (fun i => measurable_id.add_const (a i)) using 1
  simp only [gaussianReal_map_add_const, Pi.add_apply]

lemma integral_gaussianProbability (a : ℕ → ℝ) (f : (ℕ → ℝ) →ᵇ ℝ) :
    (∫ x, f x ∂(gaussianProbability a)) =
      ∫ x, f (x + a) ∂(gaussianProduct 0) := by
  change (∫ x, f x ∂(gaussianProduct a)) = _
  have hm := gaussianProduct_map_add a 0
  simp only [zero_add] at hm
  rw [← hm]
  exact integral_map (continuous_id.add_const a).measurable.aemeasurable
    f.continuous.aestronglyMeasurable

theorem continuous_gaussianProbability : Continuous gaussianProbability := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_gaussianProbability]
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun b =>
      (f.continuous.comp (continuous_id.add_const b)).aestronglyMeasurable)
  · exact ⟨‖f‖, Eventually.of_forall (fun b => ae_of_all _ (fun x => f.norm_coe_le_norm _))⟩
  · exact ae_of_all _ (fun x =>
      (f.continuous.comp (continuous_const.add continuous_id)).continuousAt)

theorem measurable_gaussianProbability :
    @Measurable (ℕ → ℝ) (ProbabilityMeasure (ℕ → ℝ)) _
      (borel (ProbabilityMeasure (ℕ → ℝ))) gaussianProbability :=
  continuous_gaussianProbability.borel_measurable.mono OpensMeasurableSpace.borel_le le_rfl

theorem gaussianProbability_mutualAC_iff (a b : ℕ → ℝ) :
    (((gaussianProbability a : Measure (ℕ → ℝ)) ≪ gaussianProbability b) ∧
      ((gaussianProbability b : Measure (ℕ → ℝ)) ≪ gaussianProbability a)) ↔
      Summable (fun n => (a n - b n) ^ 2) :=
  gaussian_mutualAC_iff_summable a b

theorem gaussian_continuous_reduction :
    Continuous gaussianProbability ∧ ∀ a b : ℕ → ℝ,
      Summable (fun n => (a n - b n) ^ 2) ↔
      (((gaussianProbability a : Measure (ℕ → ℝ)) ≪ gaussianProbability b) ∧
        ((gaussianProbability b : Measure (ℕ → ℝ)) ≪ gaussianProbability a)) :=
  ⟨continuous_gaussianProbability, fun a b => (gaussianProbability_mutualAC_iff a b).symm⟩

#print axioms continuous_gaussianProbability
#print axioms measurable_gaussianProbability
#print axioms gaussian_continuous_reduction

end MeasureEquivalenceGaussian
