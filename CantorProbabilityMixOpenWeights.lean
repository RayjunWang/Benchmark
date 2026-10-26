import PositiveProbabilityMix
import CantorPrefixPerturbation

/-! Positive finite-partition reweighting of a full-support Cantor probability. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def prefixReweightMeasure (ρ : ProbabilityMeasure HaarCantor) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) : Measure HaarCantor :=
  ∑ s : Fin n → Bool, (w s / (ρ : Measure HaarCantor) (prefixCylinder s)) •
    (ρ : Measure HaarCantor).restrict (prefixCylinder s)

lemma positive_prefix_mass_ne_zero (ρ : PositiveCylinderProbabilities)
    (n : ℕ) (s : Fin n → Bool) :
    (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder s) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (ρ.property n s)).1.ne'

lemma prefix_restriction_sum (ρ : ProbabilityMeasure HaarCantor) (n : ℕ) :
    (∑ s : Fin n → Bool, (ρ : Measure HaarCantor).restrict (prefixCylinder s)) =
      (ρ : Measure HaarCantor) := by
  have h := Measure.restrict_iUnion (μ := (ρ : Measure HaarCantor))
    (prefixCylinder_pairwise_disjoint n)
    (fun s => (isClopen_prefixCylinder s).isClosed.measurableSet)
  rw [prefixCylinder_iUnion, Measure.restrict_univ, Measure.sum_fintype] at h
  exact h.symm

lemma prefixReweightMeasure_univ (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) :
    prefixReweightMeasure ρ n w univ = ∑ s, w s := by
  simp only [prefixReweightMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply_univ]
  apply Finset.sum_congr rfl
  intro s _
  exact ENNReal.div_mul_cancel (positive_prefix_mass_ne_zero ρ n s)
    (measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _)

lemma prefixReweightMeasure_cell (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (t : Fin n → Bool) :
    prefixReweightMeasure ρ n w (prefixCylinder t) = w t := by
  classical
  simp only [prefixReweightMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply (isClopen_prefixCylinder t).isClosed.measurableSet]
  rw [Finset.sum_eq_single t]
  · rw [inter_self]
    exact ENNReal.div_mul_cancel (positive_prefix_mass_ne_zero ρ n t)
      (measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _)
  · intro s _ hst
    rw [(prefixCylinder_pairwise_disjoint n (Ne.symm hst)).inter_eq, measure_empty, mul_zero]
  · simp

lemma prefixReweightMeasure_dominates (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (hw : ∀ s, w s ≠ 0) :
    (ρ : ProbabilityMeasure HaarCantor).toMeasure ≪ prefixReweightMeasure ρ n w := by
  rw [← prefix_restriction_sum ρ n]
  rw [prefixReweightMeasure, ← Measure.sum_fintype, ← Measure.sum_fintype]
  apply Measure.absolutelyContinuous_sum_left
  intro s
  apply Measure.absolutelyContinuous_sum_right s
  apply Measure.absolutelyContinuous_smul
  exact ENNReal.div_ne_zero.mpr ⟨hw s, measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _⟩

def prefixReweightProbability (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (hw : ∑ s, w s = 1) : ProbabilityMeasure HaarCantor :=
  ⟨prefixReweightMeasure ρ n w, ⟨(prefixReweightMeasure_univ ρ n w).trans hw⟩⟩

def positivePrefixReweight (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (hw : ∑ s, w s = 1) (hpos : ∀ s, w s ≠ 0) :
    PositiveCylinderProbabilities :=
  ⟨prefixReweightProbability ρ n w hw, by
    intro m t
    have hρpos : 0 < (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder t) :=
      (ENNReal.toReal_pos_iff.mp (ρ.property m t)).1
    have hpos' := (prefixReweightMeasure_dominates ρ n w hpos).pos_mono hρpos
    exact ENNReal.toReal_pos hpos'.ne' (measure_ne_top (prefixReweightProbability ρ n w hw).toMeasure _)⟩

theorem prefixReweightMeasure_mix (t : unitInterval) (ρ : PositiveCylinderProbabilities)
    (n : ℕ) (u v : (Fin n → Bool) → ℝ≥0∞)
    (hmix : ∀ s, ENNReal.ofReal (1 - (t : ℝ)) * u s + ENNReal.ofReal (t : ℝ) * v s =
      (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder s)) :
    ENNReal.ofReal (1 - (t : ℝ)) • prefixReweightMeasure ρ n u +
      ENNReal.ofReal (t : ℝ) • prefixReweightMeasure ρ n v =
        (ρ : ProbabilityMeasure HaarCantor).toMeasure := by
  classical
  calc
    _ = ∑ s : Fin n → Bool,
        ((ENNReal.ofReal (1 - (t : ℝ)) * u s + ENNReal.ofReal (t : ℝ) * v s) /
          (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder s)) •
          (ρ : ProbabilityMeasure HaarCantor).toMeasure.restrict (prefixCylinder s) := by
      simp only [prefixReweightMeasure, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul]
      apply Finset.sum_congr rfl
      intro s _
      rw [← add_smul]
      congr 1
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ s : Fin n → Bool,
        (ρ : ProbabilityMeasure HaarCantor).toMeasure.restrict (prefixCylinder s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hmix, ENNReal.div_self (positive_prefix_mass_ne_zero ρ n s)
        (measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _), one_smul]
    _ = _ := prefix_restriction_sum ρ n

end BenchmarkJump

#print axioms BenchmarkJump.positivePrefixReweight
#print axioms BenchmarkJump.prefixReweightMeasure_mix
