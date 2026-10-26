import MeasureRowClosure
import PositiveProbabilityMix

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def halfUnitInterval : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem positiveProbabilityMix_half_measure (μ ν : PositiveCylinderProbabilities) :
    ((positiveProbabilityMix halfUnitInterval μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  ext A hA
  change ENNReal.ofReal (1 - (halfUnitInterval : ℝ)) *
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A +
      ENNReal.ofReal (halfUnitInterval : ℝ) *
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = _
  simp only [measureMidpoint, Measure.smul_apply, Measure.add_apply, ENNReal.smul_def,
    smul_eq_mul, halfUnitInterval]
  norm_num
  rw [mul_add]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- Actual Hellinger-close equivalent endpoints lift into the proved open
bundle tube over their midpoint, after reciprocal continuous reweighting. -/
theorem measure_midpoint_fiber_lift
    (W : Set PositiveDensityBundle) (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (μ₁ μ₂ σ ρ : PositiveCylinderProbabilities)
    (hσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hRew : continuousSquareReweight w hw ρ = σ) (hρU : ρ ∈ U)
    (h₁ : FullSupportMeasureEquivalence μ₁ σ) (h₂ : FullSupportMeasureEquivalence μ₂ σ)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2) :
    ∃ p : OpenFiberSquare (fun z : W => densitySource z), measureFiberEndpoints W p = (μ₁, μ₂) := by
  let κ : Measure HaarCantor := ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  have hκ₁ : ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ :=
    Measure.AbsolutelyContinuous.rfl.add_right _
  have hκ₂ : ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ :=
    Measure.AbsolutelyContinuous.rfl.add_right' _
  have hκσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ := by
    intro A hA
    rw [hσ]
    change ((1 / 2 : ℝ≥0) • κ) A = 0
    rw [Measure.smul_apply, hA, smul_zero]
  have hρσ := densitySource_target_equivalent (positiveContinuousSection w hw ρ)
  change FullSupportMeasureEquivalence ρ (continuousSquareReweight w hw ρ) at hρσ
  rw [hRew] at hρσ
  have hMid₁ := hellinger_energy_midpoint
    ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
  rw [← hσ] at hMid₁
  have hσswap : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
    rw [hσ, measureMidpoint, measureMidpoint, add_comm]
  have hMid₂ := hellinger_energy_midpoint
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
  rw [← hσswap, MeasureEquivalenceHellinger.energy_symm
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ] at hMid₂
  have hLift (μ : PositiveCylinderProbabilities) (hμσ : FullSupportMeasureEquivalence μ σ)
      (hμκ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ)
      (hMid : MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ ≤
        (1 / 2 : ℝ) * MeasureEquivalenceHellinger.energy
          ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ) :
      ∃ z : W, densitySource z = ρ ∧ densityTarget z = μ := by
    have hμρ := hμσ.1.trans hρσ.2
    have hρμ := hρσ.1.trans hμσ.2
    let z := positiveDensityPoint ρ μ hμρ hρμ
    have hSq := positiveDensityPoint_section_dist_sq ρ μ hμρ hρμ w hw
    rw [hRew] at hSq
    have hReference := MeasureEquivalenceHellinger.energy_reference_independent
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
        hμρ hρσ.2 hμκ hκσ
    have hNear : dist (densityVector z) (normalizedContinuousVector ρ w) < ε := by
      have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
      have hESmall : MeasureEquivalenceHellinger.energy
          ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) < ε ^ 2 := by
        rw [hReference]
        exact lt_of_le_of_lt hMid (by nlinarith only [hE, hεsq])
      have hdistSq : dist (densityVector z) (normalizedContinuousVector ρ w) ^ 2 < ε ^ 2 :=
        hSq.trans_lt hESmall
      exact (sq_lt_sq₀ dist_nonneg hε.le).mp hdistSq
    have hzW : z ∈ W := hTube z hρU hNear
    exact ⟨⟨z, hzW⟩, rfl, densityTarget_positiveDensityPoint ρ μ hμρ hρμ⟩
  obtain ⟨z₁, hs₁, ht₁⟩ := hLift μ₁ h₁ hκ₁ hMid₁
  obtain ⟨z₂, hs₂, ht₂⟩ := hLift μ₂ h₂ hκ₂ hMid₂
  exact ⟨⟨(z₁, z₂), hs₁.trans hs₂.symm⟩, Prod.ext ht₁ ht₂⟩

#print axioms measure_midpoint_fiber_lift

end BenchmarkJump
