import CantorHaarCylinders
import Mathlib.Probability.ProductMeasure

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BenchmarkJump

def fairCantorLaw : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fairCantorLaw_probability : IsProbabilityMeasure fairCantorLaw := by
  constructor
  norm_num [fairCantorLaw,ENNReal.inv_two_add_inv_two]

theorem fairCantorLaw_singleton (b : Bool) : fairCantorLaw {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairCantorLaw,Measure.dirac_apply]

def fairCantorProbability : ProbabilityMeasure HaarCantor :=
  ⟨Measure.infinitePi (fun _ : ℕ => fairCantorLaw),inferInstance⟩

theorem fairCantorProbability_prefix {n : ℕ} (s : Fin n → Bool) :
    (fairCantorProbability : Measure HaarCantor) (prefixCylinder s) = (1 / 2 : ℝ≥0∞) ^ n := by
  classical
  let sets : ℕ → Set Bool := fun i => if hi : i < n then {s ⟨i,hi⟩} else univ
  have he : prefixCylinder s = (Finset.range n : Set ℕ).pi sets := by
    ext x
    constructor
    · intro hx i hi
      have hin := Finset.mem_range.mp hi
      simpa [sets,hin] using hx ⟨i,hin⟩
    · intro hx i
      have h := hx i (Finset.mem_range.mpr i.isLt)
      simpa [sets,i.isLt] using h
  rw [he]
  change Measure.infinitePi (fun _ : ℕ => fairCantorLaw) ((Finset.range n : Set ℕ).pi sets) = _
  rw [Measure.infinitePi_pi _ (fun i hi => by simp [sets,Finset.mem_range.mp hi])]
  have ht : ∀ i ∈ Finset.range n, fairCantorLaw (sets i) = (1 / 2 : ℝ≥0∞) := by
    intro i hi
    simp [sets,Finset.mem_range.mp hi,fairCantorLaw_singleton]
  simp_rw [Finset.prod_congr rfl ht]
  simp

theorem fairCantorProbability_fullSupport : fairCantorProbability ∈ PositiveCylinderProbabilities := by
  intro n s
  rw [measureReal_def,fairCantorProbability_prefix,ENNReal.toReal_pow]
  norm_num

def fairFullSupportProbability : PositiveCylinderProbabilities :=
  ⟨fairCantorProbability,fairCantorProbability_fullSupport⟩

instance positiveCylinderProbabilities_nonempty : Nonempty PositiveCylinderProbabilities :=
  ⟨fairFullSupportProbability⟩

end BenchmarkJump

#print axioms BenchmarkJump.fairCantorProbability_fullSupport
