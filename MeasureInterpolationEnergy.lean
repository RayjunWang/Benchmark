import MeasureSmallPairBound
import CircleChartConstancy

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem positiveProbabilityMix_one (μ ν : PositiveCylinderProbabilities) :
    positiveProbabilityMix 1 μ ν = ν := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  change ENNReal.ofReal (1 - ((1 : unitInterval) : ℝ)) *
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A +
      ENNReal.ofReal ((1 : unitInterval) : ℝ) *
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = _
  simp

theorem positiveProbabilityMix_ac_sum (t : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) := by
  intro A hA
  have hZero := add_eq_zero.mp hA
  change ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = 0 ∧
    ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = 0 at hZero
  change (cantorProbabilityMix t μ ν : Measure HaarCantor) A = 0
  rw [cantorProbabilityMix_apply, hZero.1, hZero.2, mul_zero, mul_zero, add_zero]

theorem positiveProbabilityMix_energy_le (t u : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    MeasureEquivalenceHellinger.energy
      ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) ≤
      2 * |(t : ℝ) - (u : ℝ)| := by
  have hReference := MeasureEquivalenceHellinger.energy_reference_independent
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    (((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
      ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (Measure.AbsolutelyContinuous.rfl.add_right _) (Measure.AbsolutelyContinuous.rfl.add_right' _)
    (positiveProbabilityMix_ac_sum t μ ν) (positiveProbabilityMix_ac_sum u μ ν)
  rw [hReference, positiveProbabilityMix_measure, positiveProbabilityMix_measure]
  exact hellinger_energy_blend_le _ _ _ _ t.property.2 u.property.2

def positiveChainParameter (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) : unitInterval :=
  ⟨chainParameter m hm j, chainParameter_nonneg m hm j, chainParameter_le_one m hm j⟩

theorem positiveChainParameter_zero (m : ℕ) (hm : 0 < m) : positiveChainParameter m hm 0 = 0 := by
  apply Subtype.ext
  simp only [positiveChainParameter, chainParameter, Fin.val_zero, Nat.cast_zero, zero_div]
  rfl

theorem positiveChainParameter_last (m : ℕ) (hm : 0 < m) :
    positiveChainParameter m hm (Fin.last m) = 1 := by
  apply Subtype.ext
  simp only [positiveChainParameter, chainParameter, Fin.val_last,
    div_self (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')]
  rfl

theorem positiveProbabilityMix_chain_step_energy (m : ℕ) (hm : 0 < m) (j : Fin m)
    (μ ν : PositiveCylinderProbabilities) :
    let a := positiveProbabilityMix (positiveChainParameter m hm j.castSucc) μ ν
    let b := positiveProbabilityMix (positiveChainParameter m hm j.succ) μ ν
    MeasureEquivalenceHellinger.energy
      ((a : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((b : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((a : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((b : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) ≤ 2 / (m : ℝ) := by
  have h := positiveProbabilityMix_energy_le (positiveChainParameter m hm j.castSucc)
    (positiveChainParameter m hm j.succ) μ ν
  change _ ≤ 2 * |chainParameter m hm j.castSucc - chainParameter m hm j.succ| at h
  rw [chainParameter_step m hm j] at h
  simpa only [mul_one_div] using h

#print axioms positiveProbabilityMix_energy_le
#print axioms positiveProbabilityMix_chain_step_energy

end BenchmarkJump
