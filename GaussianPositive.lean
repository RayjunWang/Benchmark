import SnowflakeReduction
import GaussianCanonical

/-! Positive continuous reductions for p-summable difference, 0<p<=2,
to actual mutual absolute continuity on ProbabilityMeasure (Nat -> Real).
The sample-space transfer to Cantor space is a separate statement.
-/

open MeasureTheory
open scoped Topology

namespace MeasureEquivalenceGaussian

theorem exists_continuous_gaussian_reduction_of_pos_le_two (p : ℝ)
    (hp0 : 0 < p) (hp2 : p ≤ 2) :
    ∃ G : (ℕ → ℝ) → ProbabilityMeasure (ℕ → ℝ), Continuous G ∧ Measurable G ∧ ∀ x y : ℕ → ℝ,
      Summable (fun n => |x n - y n| ^ p) ↔
        (((G x : Measure (ℕ → ℝ)) ≪ G y) ∧ ((G y : Measure (ℕ → ℝ)) ≪ G x)) := by
  by_cases hp : p = 2
  · subst p
    refine ⟨gaussianProbability, continuous_gaussianProbability,
      measurable_gaussianProbability_canonical, ?_⟩
    intro x y
    simpa only [Real.rpow_two, sq_abs] using (gaussianProbability_mutualAC_iff x y).symm
  · obtain ⟨R, hR, hiff⟩ := MeasureEquivalenceSnowflake.exists_continuous_reduction_to_square
      p hp0 (lt_of_le_of_ne hp2 hp)
    refine ⟨fun x => gaussianProbability (R x), continuous_gaussianProbability.comp hR,
      measurable_gaussianProbability_canonical.comp hR.measurable, ?_⟩
    intro x y
    exact (hiff x y).trans (gaussianProbability_mutualAC_iff (R x) (R y)).symm

theorem exists_continuous_gaussian_reduction_one_le (p : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ G : (ℕ → ℝ) → ProbabilityMeasure (ℕ → ℝ), Continuous G ∧ Measurable G ∧ ∀ x y : ℕ → ℝ,
      Summable (fun n => |x n - y n| ^ p) ↔
        (((G x : Measure (ℕ → ℝ)) ≪ G y) ∧ ((G y : Measure (ℕ → ℝ)) ≪ G x)) :=
  exists_continuous_gaussian_reduction_of_pos_le_two p (lt_of_lt_of_le zero_lt_one hp1) hp2

#print axioms exists_continuous_gaussian_reduction_of_pos_le_two
#print axioms exists_continuous_gaussian_reduction_one_le

end MeasureEquivalenceGaussian
