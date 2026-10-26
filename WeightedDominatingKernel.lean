import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace SpectralDomination

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def weight (μ : ℕ → Measure Y) (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ (n + 1) * (1 + μ n univ)⁻¹

def weightedKernel (μ : X → ℕ → Measure Y)
    (hm : ∀ n, Measurable (fun x => μ x n)) (n : ℕ) : Kernel X Y where
  toFun x := weight (μ x) n • μ x n
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun x => weight (μ x) n * μ x n s)
    apply Measurable.mul
    · exact measurable_const.mul
        (measurable_const.add ((Measure.measurable_coe MeasurableSet.univ).comp (hm n))).inv
    · exact (Measure.measurable_coe hs).comp (hm n)

theorem weightedKernel_mass_le (μ : X → ℕ → Measure Y) (hm) (n : ℕ) (x : X) :
    weightedKernel μ hm n x univ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
  change ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * (1 + μ x n univ)⁻¹) * μ x n univ ≤ _
  rw [mul_assoc]
  calc
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((1 + μ x n univ)⁻¹ * (1 + μ x n univ)) := by gcongr; exact le_add_self
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) * 1 := by gcongr; exact ENNReal.inv_mul_le_one _
    _ = _ := mul_one _

instance weightedKernel_finite (μ : X → ℕ → Measure Y)
    (hm : ∀ n, Measurable (fun x => μ x n)) (n : ℕ) :
    IsFiniteKernel (weightedKernel μ hm n) :=
  ⟨⟨(2⁻¹ : ℝ≥0∞) ^ (n + 1), by finiteness, weightedKernel_mass_le μ hm n⟩⟩

def dominatingKernel (μ : X → ℕ → Measure Y)
    (hm : ∀ n, Measurable (fun x => μ x n)) (base : Y) : Kernel X Y :=
  Kernel.const X (Measure.dirac base) + Kernel.sum (weightedKernel μ hm)

theorem dominatingKernel_mass_le (μ : X → ℕ → Measure Y) (hm) (base : Y) (x : X) :
    dominatingKernel μ hm base x univ ≤ 2 := by
  simp only [dominatingKernel, Kernel.add_apply, Kernel.const_apply, Measure.add_apply,
    Measure.dirac_apply_of_mem (mem_univ base), Kernel.sum_apply' _ _ MeasurableSet.univ]
  have hsum : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1)) = 1 := by
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by finiteness)
  calc
    _ ≤ 1 + ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) := add_le_add le_rfl
      (ENNReal.tsum_le_tsum (fun n => weightedKernel_mass_le μ hm n x))
    _ = 2 := by rw [hsum]; norm_num

instance dominatingKernel_finite (μ : X → ℕ → Measure Y) (hm) (base : Y) :
    IsFiniteKernel (dominatingKernel μ hm base) :=
  ⟨⟨2, by norm_num, dominatingKernel_mass_le μ hm base⟩⟩

theorem weight_ne_zero (μ : ℕ → Measure Y) [∀ n, IsFiniteMeasure (μ n)] (n : ℕ) :
    weight μ n ≠ 0 := by
  simp only [weight, ne_eq, mul_eq_zero, pow_eq_zero_iff', ENNReal.inv_eq_zero,
    ENNReal.add_eq_top]
  simp [measure_ne_top]

theorem measure_ac_dominatingKernel (μ : X → ℕ → Measure Y) (hm) (base : Y)
    [∀ x n, IsFiniteMeasure (μ x n)] (x : X) (n : ℕ) :
    μ x n ≪ dominatingKernel μ hm base x := by
  have hscale : μ x n ≪ weightedKernel μ hm n x :=
    Measure.absolutelyContinuous_smul (weight_ne_zero (μ x) n)
  have hsum : weightedKernel μ hm n x ≪ Kernel.sum (weightedKernel μ hm) x := by
    rw [Kernel.sum_apply]
    exact Measure.absolutelyContinuous_sum_right n Measure.AbsolutelyContinuous.rfl
  exact (hscale.trans hsum).add_right' _

end SpectralDomination

#print axioms SpectralDomination.measure_ac_dominatingKernel
