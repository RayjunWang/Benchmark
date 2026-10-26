import CantorProbabilityMix
import HellingerConvexEstimates

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def positiveProbabilityMix (t : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    PositiveCylinderProbabilities :=
  ⟨cantorProbabilityMix t μ ν, by
    by_cases ht : 0 < (t : ℝ)
    · exact cantorProbabilityMix_fullSupport_right t ht μ ν
    · have ht0 : (t : ℝ) = 0 := le_antisymm (not_lt.mp ht) t.property.1
      intro n s
      rw [cantorProbabilityMix_real, ht0]
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using μ.property n s⟩

theorem continuous_positiveProbabilityMix :
    Continuous (fun p : unitInterval × (PositiveCylinderProbabilities × PositiveCylinderProbabilities) =>
      positiveProbabilityMix p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  exact continuous_cantorProbabilityMix.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

theorem positiveProbabilityMix_self (t : unitInterval) (μ : PositiveCylinderProbabilities) :
    positiveProbabilityMix t μ μ = μ := Subtype.ext (cantorProbabilityMix_self t μ)

theorem positiveProbabilityMix_measure (t : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureBlend (⟨(t : ℝ), t.property.1⟩ : ℝ≥0)
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  let r : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
  have hr : r ≤ 1 := t.property.2
  have hA : ((1 - r : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 - (t : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub hr, NNReal.coe_one]
    rfl
  have hB : (r : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_coe_nnreal.symm
  change ENNReal.ofReal (1 - (t : ℝ)) • (μ : ProbabilityMeasure HaarCantor).toMeasure +
      ENNReal.ofReal (t : ℝ) • (ν : ProbabilityMeasure HaarCantor).toMeasure =
    (1 - r) • (μ : ProbabilityMeasure HaarCantor).toMeasure +
      r • (ν : ProbabilityMeasure HaarCantor).toMeasure
  ext A hAm
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hA, hB]

theorem positiveProbabilityMix_ac (t : unitInterval) (μ ν ρ : PositiveCylinderProbabilities)
    (hμ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hν : ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  intro A hA
  change (cantorProbabilityMix t μ ν : Measure HaarCantor) A = 0
  rw [cantorProbabilityMix_apply, hμ hA, hν hA, mul_zero, mul_zero, add_zero]

theorem right_ac_positiveProbabilityMix (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ ν : PositiveCylinderProbabilities) :
    ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  intro A hA
  change ENNReal.ofReal (1 - (t : ℝ)) *
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A + ENNReal.ofReal (t : ℝ) *
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = 0 at hA
  exact (mul_eq_zero.mp (add_eq_zero.mp hA).2).resolve_left (ENNReal.ofReal_pos.mpr ht).ne'

#print axioms continuous_positiveProbabilityMix
#print axioms positiveProbabilityMix_measure

end BenchmarkJump
