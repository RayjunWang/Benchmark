import CantorCylinderRefinement
import ContinuousSquareReweight

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def prefixStep {n : ℕ} (a : (Fin n → Bool) → ℝ) : C(HaarCantor,ℝ) :=
  ⟨fun x => a (fun i : Fin n => x i),
    (continuous_of_discreteTopology (f := a)).comp (continuous_pi fun i : Fin n => continuous_apply (i : ℕ))⟩

theorem prefixStep_on_cell {n : ℕ} (a : (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (x : HaarCantor) (hx : x ∈ prefixCylinder s) : prefixStep a x = a s := by
  change a (fun i : Fin n => x i) = a s
  congr 1
  exact funext hx

theorem prefixStep_eq_indicator_sum {n : ℕ} (a : (Fin n → Bool) → ℝ) (x : HaarCantor) :
    prefixStep a x = ∑ s : Fin n → Bool, (prefixCylinder s).indicator (fun _ => a s) x := by
  classical
  let s₀ : Fin n → Bool := fun i => x i
  rw [Finset.sum_eq_single s₀]
  · simp [prefixStep,s₀,prefixCylinder]
  · intro s _hs hne
    have hx : x ∉ prefixCylinder s := by
      intro h
      exact hne (funext h).symm
    simp [Set.indicator_of_notMem hx]
  · simp

theorem integral_prefixStep {n : ℕ} (μ : Measure HaarCantor) [IsFiniteMeasure μ]
    (a : (Fin n → Bool) → ℝ) :
    (∫ x, prefixStep a x ∂μ) = ∑ s : Fin n → Bool, μ.real (prefixCylinder s) * a s := by
  have he : (fun x => prefixStep a x) = fun x => ∑ s : Fin n → Bool,
      (prefixCylinder s).indicator (fun _ => a s) x := funext (prefixStep_eq_indicator_sum a)
  rw [he,integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro s _hs
    simpa only [smul_eq_mul] using integral_indicator_const (μ := μ) (a s)
      (isClopen_prefixCylinder s).isClosed.measurableSet
  · intro s _hs
    exact (integrable_const (a s)).indicator (isClopen_prefixCylinder s).isClosed.measurableSet

theorem setIntegral_prefixStep {n : ℕ} (μ : Measure HaarCantor) [IsFiniteMeasure μ]
    (a : (Fin n → Bool) → ℝ) (s : Fin n → Bool) :
    (∫ x in prefixCylinder s, prefixStep a x ∂μ) = μ.real (prefixCylinder s) * a s := by
  calc
    _ = ∫ _x in prefixCylinder s, a s ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (isClopen_prefixCylinder s).isClosed.measurableSet] with x hx
      exact prefixStep_on_cell a s x hx
    _ = _ := by rw [setIntegral_const,smul_eq_mul]

end BenchmarkJump

#print axioms BenchmarkJump.integral_prefixStep
