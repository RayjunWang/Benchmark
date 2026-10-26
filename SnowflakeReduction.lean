import SnowflakeIntegral
import HilbertCoordinates
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Actual continuous reductions of p-summable difference to square-summable
difference on the ambient product space of all real sequences.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureEquivalenceSnowflake

instance halfLine_sigmaFinite : SigmaFinite halfLine := by
  unfold halfLine
  infer_instance

theorem exists_continuous_sequence_snowflake (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) :
    ∃ J : ℝ → (ℕ → ℝ), Continuous J ∧ ∀ t u : ℝ,
      HasSum (fun k => (J t k - J u k) ^ 2) (energy p 1 * |t - u| ^ p) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨F, hF, hnorm⟩ :=
    MeasureEquivalenceHilbertCoordinates.exists_continuous_coordinates
      (H := Lp ℂ 2 halfLine)
  refine ⟨fun t => F (embedding p hp0 hp2 t), hF.comp (continuous_embedding p hp0 hp2), ?_⟩
  intro t u
  simpa only [embedding_norm_sub_sq] using
    hnorm (embedding p hp0 hp2 t) (embedding p hp0 hp2 u)

theorem exists_continuous_reduction_to_square (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) :
    ∃ R : (ℕ → ℝ) → (ℕ → ℝ), Continuous R ∧ ∀ x y : ℕ → ℝ,
      Summable (fun n => |x n - y n| ^ p) ↔
        Summable (fun m => (R x m - R y m) ^ 2) := by
  obtain ⟨J, hJ, hrow⟩ := exists_continuous_sequence_snowflake p hp0 hp2
  let R : (ℕ → ℝ) → (ℕ → ℝ) := fun x m => J (x (Nat.unpair m).1) (Nat.unpair m).2
  refine ⟨R, ?_, ?_⟩
  · apply continuous_pi
    intro m
    exact (continuous_apply (Nat.unpair m).2).comp (hJ.comp (continuous_apply (Nat.unpair m).1))
  · intro x y
    have hflat : Summable (fun m => (R x m - R y m) ^ 2) ↔
        Summable (fun q : ℕ × ℕ => (J (x q.1) q.2 - J (y q.1) q.2) ^ 2) := by
      change Summable ((fun q : ℕ × ℕ => (J (x q.1) q.2 - J (y q.1) q.2) ^ 2) ∘
        Nat.pairEquiv.symm) ↔ _
      exact Nat.pairEquiv.symm.summable_iff
    have hprod := summable_prod_of_nonneg
      (f := fun q : ℕ × ℕ => (J (x q.1) q.2 - J (y q.1) q.2) ^ 2)
      (fun q => sq_nonneg _)
    have hsum : (fun n => ∑' k, (J (x n) k - J (y n) k) ^ 2) =
        (fun n => energy p 1 * |x n - y n| ^ p) :=
      funext (fun n => (hrow (x n) (y n)).tsum_eq)
    rw [hflat, hprod, hsum]
    constructor
    · intro h
      exact ⟨fun n => (hrow (x n) (y n)).summable, h.mul_left _⟩
    · intro h
      exact (summable_mul_left_iff (energy_one_pos p hp0 hp2).ne').1 h.2

#print axioms exists_continuous_sequence_snowflake
#print axioms exists_continuous_reduction_to_square

end MeasureEquivalenceSnowflake
