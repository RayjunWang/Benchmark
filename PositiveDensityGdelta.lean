import HaarIntegralContinuity
import CantorProbabilityTopology
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def densityClip (k : ℕ) (t : ℝ) : ℝ := min 1 ((k : ℝ) * max t 0)

theorem lipschitz_densityClip (k : ℕ) : LipschitzWith (k : ℝ≥0) (densityClip k) := by
  have hm : LipschitzWith (k : ℝ≥0) (fun t : ℝ => (k : ℝ) * max t 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h
    calc
      dist ((k : ℝ) * max x 0) ((k : ℝ) * max y 0) =
          (k : ℝ) * dist (max x 0) (max y 0) := by
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity), Real.dist_eq]
      _ ≤ (k : ℝ) * dist x y := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((k : ℝ≥0) : ℝ) * dist x y := rfl
  exact hm.const_min 1

theorem densityClip_zero (k : ℕ) : densityClip k 0 = 0 := by simp [densityClip]

theorem densityClip_nonneg (k : ℕ) (t : ℝ) : 0 ≤ densityClip k t := by
  unfold densityClip
  positivity

theorem densityClip_le_one (k : ℕ) (t : ℝ) : densityClip k t ≤ 1 := min_le_left _ _

theorem densityClip_tendsto (t : ℝ) :
    Tendsto (fun k : ℕ => densityClip k t) atTop (𝓝 (if 0 < t then (1 : ℝ) else 0)) := by
  by_cases ht : 0 < t
  · simp only [if_pos ht]
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkt : 1 ≤ (k : ℝ) * t := by
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
      have hdiv : 1 / t ≤ (k : ℝ) := hN.trans hNk
      exact (div_le_iff₀ ht).mp hdiv
    simp only [densityClip, max_eq_left ht.le, min_eq_left hkt]
  · simp only [if_neg ht]
    have ht0 : t ≤ 0 := le_of_not_gt ht
    simpa only [densityClip, max_eq_right ht0, mul_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

def positiveIndicator (t : ℝ) : ℝ := if 0 < t then 1 else 0

theorem densityClip_le_positiveIndicator (k : ℕ) (t : ℝ) :
    densityClip k t ≤ positiveIndicator t := by
  by_cases ht : 0 < t
  · simpa only [positiveIndicator, if_pos ht] using densityClip_le_one k t
  · simp [positiveIndicator, ht, densityClip, max_eq_right (le_of_not_gt ht)]

theorem integrable_positiveIndicator {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    Integrable (fun x => positiveIndicator (f x)) μ := by
  have hs : MeasurableSet {x | 0 < f x} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).measurable
  simpa only [positiveIndicator, Set.indicator_apply] using
    (integrable_const (1 : ℝ)).indicator hs

theorem integrable_densityClip {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (k : ℕ) :
    Integrable (fun x => densityClip k (f x)) μ :=
  MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((lipschitz_densityClip k).comp_memLp (densityClip_zero k) (Lp.memLp f))

theorem tendsto_integral_densityClip {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    Tendsto (fun k : ℕ => ∫ x, densityClip k (f x) ∂μ) atTop
      (𝓝 (∫ x, positiveIndicator (f x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro k
    exact ((lipschitz_densityClip k).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  · exact integrable_const 1
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (densityClip_nonneg k (f x))]
      exact densityClip_le_one k (f x)
  · exact Eventually.of_forall fun x => densityClip_tendsto (f x)

/-- Strict positivity almost everywhere is detected by a countable family
of strict integral inequalities; no nonnegative-cone assumption is needed. -/
theorem ae_positive_iff_densityClip {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∀ᵐ x ∂μ, 0 < f x) ↔
      ∀ r : ℕ, ∃ k : ℕ,
        1 - 1 / (r + 1 : ℝ) < ∫ x, densityClip k (f x) ∂μ := by
  classical
  let I : ℝ := ∫ x, positiveIndicator (f x) ∂μ
  have hI : I ≤ 1 := by
    have h := integral_mono (integrable_positiveIndicator μ f) (integrable_const (1 : ℝ))
      (fun x => by unfold positiveIndicator; split_ifs <;> norm_num)
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using h
  constructor
  · intro hPos r
    have hIone : I = 1 := by
      have hae : (fun x => positiveIndicator (f x)) =ᵐ[μ] fun _ => (1 : ℝ) :=
        hPos.mono fun x hx => by simp only [positiveIndicator, if_pos hx]
      simpa only [I, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
        integral_congr_ae hae
    have hLim : Tendsto (fun k : ℕ => ∫ x, densityClip k (f x) ∂μ) atTop (𝓝 (1 : ℝ)) := by
      simpa only [← hIone] using tendsto_integral_densityClip μ f
    have hlt : 1 - 1 / (r + 1 : ℝ) < 1 := by
      have hpos : 0 < 1 / (r + 1 : ℝ) := by positivity
      linarith
    exact ((tendsto_order.mp hLim).1 _ hlt).exists
  · intro hTests
    have hIone : I = 1 := by
      apply le_antisymm hI
      by_contra! hIlow
      obtain ⟨r, hr⟩ := exists_nat_one_div_lt (sub_pos.mpr hIlow)
      obtain ⟨k, hk⟩ := hTests r
      have hClip : (∫ x, densityClip k (f x) ∂μ) ≤ I :=
        integral_mono (integrable_densityClip μ f k) (integrable_positiveIndicator μ f)
          (fun x => densityClip_le_positiveIndicator k (f x))
      linarith
    have hnon : ∀ x, 0 ≤ 1 - positiveIndicator (f x) := by
      intro x
      unfold positiveIndicator
      split_ifs <;> norm_num
    have hIntZero : (∫ x, 1 - positiveIndicator (f x) ∂μ) = 0 := by
      rw [integral_sub (integrable_const 1) (integrable_positiveIndicator μ f)]
      simpa only [I, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
        sub_eq_zero.mpr hIone.symm
    have hAe := (integral_eq_zero_iff_of_nonneg hnon
      ((integrable_const 1).sub (integrable_positiveIndicator μ f))).mp hIntZero
    filter_upwards [hAe] with x hx
    by_contra hnot
    simp only [positiveIndicator, if_neg hnot] at hx
    norm_num at hx

def StrictPositiveHaarParameters : Set (PositiveCylinderProbabilities × HaarCoefficientSpace) :=
  {p | ∀ᵐ x ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor), 0 < haarLift p.1 p.2 x}

theorem isGδ_strictPositiveHaarParameters : IsGδ StrictPositiveHaarParameters := by
  have heq : StrictPositiveHaarParameters = ⋂ r : ℕ, ⋃ k : ℕ,
      {p : PositiveCylinderProbabilities × HaarCoefficientSpace |
        1 - 1 / (r + 1 : ℝ) <
          haarLipschitzIntegral (densityClip k) (lipschitz_densityClip k) (densityClip_zero k) p.1 p.2} := by
    ext p
    simp only [StrictPositiveHaarParameters, mem_setOf_eq, mem_iInter, mem_iUnion,
      ae_positive_iff_densityClip, haarLipschitzIntegral_eq_integral]
  rw [heq]
  apply IsGδ.iInter_of_isOpen
  intro r
  apply isOpen_iUnion
  intro k
  exact isOpen_lt continuous_const
    (continuous_haarLipschitzIntegral (densityClip k) (lipschitz_densityClip k) (densityClip_zero k))

#print axioms ae_positive_iff_densityClip
#print axioms isGδ_strictPositiveHaarParameters

end BenchmarkJump
