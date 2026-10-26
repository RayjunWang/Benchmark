import CantorHaarCylinders

open MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkJump

def lowerMassChild (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) : Bool := by
  classical
  exact if (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s false)) ≤
      (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s true)) then false else true

theorem prefixCylinder_mass_split (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) :
    (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s false)) +
      (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s true)) =
      (μ : Measure HaarCantor).real (prefixCylinder s) := by
  rw [← measureReal_union (prefixCylinder_children_disjoint s) (isClopen_prefixCylinder _).isClosed.measurableSet,
    prefixCylinder_split]

theorem lowerMassChild_bound (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) :
    (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s (lowerMassChild μ s))) ≤
      (μ : Measure HaarCantor).real (prefixCylinder s) / 2 := by
  classical
  have hs := prefixCylinder_mass_split μ s
  unfold lowerMassChild
  split_ifs with h
  · linarith
  · linarith

def smallMassPrefix (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) :
    (m : ℕ) → Fin (n + m) → Bool
  | 0 => s
  | m + 1 => Fin.snoc (smallMassPrefix μ s m) (lowerMassChild μ (smallMassPrefix μ s m))

theorem smallMassPrefix_subset (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) (m : ℕ) :
    prefixCylinder (smallMassPrefix μ s m) ⊆ prefixCylinder s := by
  induction m with
  | zero => exact Subset.rfl
  | succ m ih =>
    intro x hx
    apply ih
    exact ((mem_prefixCylinder_snoc _ _ x).mp hx).1

theorem smallMassPrefix_bound (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) (m : ℕ) :
    (μ : Measure HaarCantor).real (prefixCylinder (smallMassPrefix μ s m)) ≤
      (1 / 2 : ℝ) ^ m * (μ : Measure HaarCantor).real (prefixCylinder s) := by
  induction m with
  | zero => simp [smallMassPrefix]
  | succ m ih =>
    have hc := lowerMassChild_bound μ (smallMassPrefix μ s m)
    change (μ : Measure HaarCantor).real
      (prefixCylinder (Fin.snoc (smallMassPrefix μ s m) (lowerMassChild μ (smallMassPrefix μ s m)))) ≤ _
    rw [pow_succ]
    nlinarith

end BenchmarkJump

#print axioms BenchmarkJump.smallMassPrefix_bound
