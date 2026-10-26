import ClopenHaarNode
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

/-- A Haar difference is orthogonal to every L2 function constant on its
parent cell. The function may be arbitrary outside that cell. -/
theorem splitHaar_inner_eq_zero_of_constant_on_parent
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (g : Lp ℝ 2 μ) (c : ℝ)
    (hg : ∀ᵐ x ∂μ, x ∈ A ∪ B → g x = c) :
    inner ℝ (splitHaar μ A B hA hB) g = 0 := by
  have hIA : inner ℝ (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)) g =
      μ.real A * c := by
    rw [L2.inner_indicatorConstLp_one]
    have heq : (∫ x in A, g x ∂μ) = ∫ _ in A, c ∂μ :=
      setIntegral_congr_ae hA (hg.mono fun x hx hxA => hx (Or.inl hxA))
    rw [heq, setIntegral_const, smul_eq_mul]
  have hIB : inner ℝ (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)) g =
      μ.real B * c := by
    rw [L2.inner_indicatorConstLp_one]
    have heq : (∫ x in B, g x ∂μ) = ∫ _ in B, c ∂μ :=
      setIntegral_congr_ae hB (hg.mono fun x hx hxB => hx (Or.inr hxB))
    rw [heq, setIntegral_const, smul_eq_mul]
  unfold splitHaar
  simp only [inner_smul_left, inner_sub_left, RCLike.conj_to_real, hIA, hIB]
  ring

#print axioms splitHaar_inner_eq_zero_of_constant_on_parent

end BenchmarkJump
