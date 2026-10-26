import CantorHaarOrthogonal
import CantorHaarSpan

open MeasureTheory Set
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def cantorHaarFamily (μ : PositiveCylinderProbabilities) :
    Option HaarNodeIndex → Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  | none => cantorOneVector μ
  | some i => cantorHaarNode μ i

theorem cantorOneVector_norm (μ : PositiveCylinderProbabilities) : ‖cantorOneVector μ‖ = 1 := by
  have hinner : inner ℝ (cantorOneVector μ) (cantorOneVector μ) = 1 := by
    simp only [cantorOneVector, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
      inter_self]
    simp
  rw [real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (cantorOneVector μ)]

theorem cantorHaarFamily_orthonormal (μ : PositiveCylinderProbabilities) :
    Orthonormal ℝ (cantorHaarFamily μ) := by
  constructor
  · intro i
    cases i with
    | none => exact cantorOneVector_norm μ
    | some i => exact cantorHaarNode_norm μ i
  · intro i j hne
    cases i with
    | none =>
        cases j with
        | none => exact False.elim (hne rfl)
        | some j =>
            rw [real_inner_comm]
            exact cantorHaarNode_inner_one μ j
    | some i =>
        cases j with
        | none => exact cantorHaarNode_inner_one μ i
        | some j =>
            exact (cantorHaarNode_orthonormal μ).inner_eq_zero
              (fun hij => hne (congrArg some hij))

theorem range_cantorHaarFamily (μ : PositiveCylinderProbabilities) :
    range (cantorHaarFamily μ) = {cantorOneVector μ} ∪ range (cantorHaarNode μ) := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩
  · rintro (hf | ⟨i, rfl⟩)
    · exact ⟨none, mem_singleton_iff.mp hf |>.symm⟩
    · exact ⟨some i, rfl⟩

theorem span_cantorHaarFamily (μ : PositiveCylinderProbabilities) :
    Submodule.span ℝ (range (cantorHaarFamily μ)) = cantorHaarSpan μ := by
  rw [range_cantorHaarFamily]
  rfl

#print axioms cantorHaarFamily_orthonormal

end BenchmarkJump
