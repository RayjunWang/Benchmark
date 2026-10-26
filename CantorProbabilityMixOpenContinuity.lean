import CantorProbabilityMixOpenWeights
import CantorCylinderRefinement

/-! Weak continuity of the positive finite-cell reweighting operation. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def realPrefixReweight (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ) (hw : ∑ s, w s = 1) (hpos : ∀ s, 0 < w s) :
    PositiveCylinderProbabilities :=
  positivePrefixReweight ρ n (fun s => ENNReal.ofReal (w s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => (hpos s).le), hw, ENNReal.ofReal_one])
    (fun s => (ENNReal.ofReal_pos.mpr (hpos s)).ne')

lemma realPrefixReweight_real (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ) (hw : ∑ s, w s = 1) (hpos : ∀ s, 0 < w s)
    (A : Set HaarCantor) (hA : MeasurableSet A) :
    ((realPrefixReweight ρ n w hw hpos : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real A =
      ∑ s : Fin n → Bool, (w s /
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)) *
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (A ∩ prefixCylinder s) := by
  change (prefixReweightMeasure ρ n (fun s => ENNReal.ofReal (w s)) A).toReal = _
  rw [prefixReweightMeasure, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro s _
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (hpos s).le, Measure.restrict_apply hA, measureReal_def]
  · intro s _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top
      (ENNReal.div_ne_top ENNReal.ofReal_ne_top (positive_prefix_mass_ne_zero ρ n s))
      (measure_ne_top (((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).restrict (prefixCylinder s)) A)

theorem continuous_realPrefixReweight {T : Type*} [TopologicalSpace T]
    (ρ : T → PositiveCylinderProbabilities) (hρ : Continuous ρ)
    (n : ℕ) (w : T → (Fin n → Bool) → ℝ) (hwc : ∀ s, Continuous (fun x => w x s))
    (hw : ∀ x, ∑ s, w x s = 1) (hpos : ∀ x s, 0 < w x s) :
    Continuous (fun x => realPrefixReweight (ρ x) n (w x) (hw x) (hpos x)) := by
  apply Continuous.subtype_mk
  apply (continuous_cantorProbability_iff _).mpr
  intro k
  change Continuous (fun x =>
    ((realPrefixReweight (ρ x) n (w x) (hw x) (hpos x) : ProbabilityMeasure HaarCantor) :
      Measure HaarCantor).real (MeasureUnitary.cantorCylinder k))
  simp_rw [realPrefixReweight_real _ _ _ _ _ _ (MeasureUnitary.cantorCylinder_measurable k)]
  apply continuous_finsetSum
  intro s _
  have hc := (continuous_clopen_mass (prefixCylinder s) (isClopen_prefixCylinder s)).comp
    (continuous_subtype_val.comp hρ)
  have hi := (continuous_clopen_mass (MeasureUnitary.cantorCylinder k ∩ prefixCylinder s)
    ((isClopen_cantorCylinder k).inter (isClopen_prefixCylinder s))).comp
      (continuous_subtype_val.comp hρ)
  exact ((hwc s).div hc (fun x => (ρ x).property n s |>.ne')).mul hi

def prefixResample (ρ μ : PositiveCylinderProbabilities) (n : ℕ) : PositiveCylinderProbabilities :=
  realPrefixReweight ρ n
    (fun s => ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s))
    (prefixCylinder_mass_sum μ n) (μ.property n)

lemma prefixResample_cell (ρ μ : PositiveCylinderProbabilities) (n : ℕ) (s : Fin n → Bool) :
    ((prefixResample ρ μ n : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) =
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) := by
  change prefixReweightMeasure ρ n _ _ = _
  rw [prefixReweightMeasure_cell]
  change ENNReal.ofReal (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    (prefixCylinder s)).toReal = _
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma prefixResample_cylinder (ρ μ : PositiveCylinderProbabilities) (n : ℕ)
    (k : MeasureUnitary.CantorCylinderIndex) (hk : ∀ i ∈ k.1, i < n) :
    ((prefixResample ρ μ n : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (MeasureUnitary.cantorCylinder k) =
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) := by
  classical
  rw [cantorCylinder_mass_prefix_sum _ k n hk, cantorCylinder_mass_prefix_sum _ k n hk]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact prefixResample_cell ρ μ n s
  · rfl

theorem tendsto_prefixResample (ρ μ : PositiveCylinderProbabilities) :
    Tendsto (fun n : ℕ => prefixResample ρ μ n) atTop (𝓝 μ) := by
  apply tendsto_subtype_rng.mpr
  apply (tendsto_cantorProbability_iff _ _).mpr
  intro k
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (k.1.sup id)] with n hn
  exact congrArg ENNReal.toReal (prefixResample_cylinder ρ μ n k
    (fun i hi => (Finset.le_sup (f := id) hi).trans_lt hn)).symm

end BenchmarkJump

#print axioms BenchmarkJump.continuous_realPrefixReweight
