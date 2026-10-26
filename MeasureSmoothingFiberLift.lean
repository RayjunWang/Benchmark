import MeasureHellingerFiberLift

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem hellinger_energy_nonneg {α : Type*} [MeasurableSpace α] (μ ν ρ : Measure α) :
    0 ≤ MeasureEquivalenceHellinger.energy μ ν ρ := integral_nonneg fun _ => sq_nonneg _

theorem measure_endpoint_lift_of_energy
    (W : Set PositiveDensityBundle) (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (μ σ ρ : PositiveCylinderProbabilities) (hRew : continuousSquareReweight w hw ρ = σ)
    (hρU : ρ ∈ U) (hμρ : FullSupportMeasureEquivalence μ ρ)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) < ε ^ 2) :
    ∃ z : W, densitySource z = ρ ∧ densityTarget z = μ := by
  let z := positiveDensityPoint ρ μ hμρ.1 hμρ.2
  have hSq := positiveDensityPoint_section_dist_sq ρ μ hμρ.1 hμρ.2 w hw
  rw [hRew] at hSq
  have hNear : dist (densityVector z) (normalizedContinuousVector ρ w) < ε :=
    (sq_lt_sq₀ dist_nonneg hε.le).mp (hSq.trans_lt hE)
  exact ⟨⟨z, hTube z hρU hNear⟩, rfl, densityTarget_positiveDensityPoint ρ μ hμρ.1 hμρ.2⟩

/-- Smoothing arbitrary endpoints by a positive amount of their midpoint
produces actual same-source bundle points inside the prescribed L2 tube. -/
theorem measure_smoothing_fiber_lift
    (W : Set PositiveDensityBundle) (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (μ₁ μ₂ σ ρ : PositiveCylinderProbabilities)
    (hσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hRew : continuousSquareReweight w hw ρ = σ) (hρU : ρ ∈ U)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2)
    (r : unitInterval) (hr : 0 < (r : ℝ)) :
    ∃ p : OpenFiberSquare (fun z : W => densitySource z),
      measureFiberEndpoints W p = (positiveProbabilityMix r μ₁ σ, positiveProbabilityMix r μ₂ σ) := by
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
  have hσκ : κ ≪ ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
    intro A hA
    rw [hσ] at hA
    change ((1 / 2 : ℝ≥0) • κ) A = 0 at hA
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hA
    exact (mul_eq_zero.mp hA).resolve_left (by norm_num)
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
  have hLift (μ : PositiveCylinderProbabilities)
      (hμκ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ)
      (hMid : MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ ≤
        (1 / 2 : ℝ) * MeasureEquivalenceHellinger.energy
          ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ) :
      ∃ z : W, densitySource z = ρ ∧ densityTarget z = positiveProbabilityMix r μ σ := by
    let η := positiveProbabilityMix r μ σ
    have hησ := positiveProbabilityMix_ac r μ σ σ (hμκ.trans hσκ) Measure.AbsolutelyContinuous.rfl
    have hση := right_ac_positiveProbabilityMix r hr μ σ
    have hηρ := hησ.trans hρσ.2
    have hρη := hρσ.1.trans hση
    have hηκ := hησ.trans hκσ
    have hSmooth := hellinger_energy_smoothing
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
        (⟨(r : ℝ), r.property.1⟩ : ℝ≥0) r.property.2
    rw [← positiveProbabilityMix_measure r μ σ] at hSmooth
    have hNonneg := hellinger_energy_nonneg
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
    have hContract : (1 - (r : ℝ)) * MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ ≤
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ := by
      nlinarith only [r.property.1, hNonneg]
    have hReference := MeasureEquivalenceHellinger.energy_reference_independent
      ((η : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ hηρ hρσ.2 hηκ hκσ
    have hESmall : MeasureEquivalenceHellinger.energy
        ((η : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) < ε ^ 2 := by
      rw [hReference]
      exact lt_of_le_of_lt (hSmooth.trans (hContract.trans hMid))
        (by have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε; nlinarith only [hE, hεsq])
    exact measure_endpoint_lift_of_energy W U w hw ε hε hTube η σ ρ hRew hρU ⟨hηρ, hρη⟩ hESmall
  obtain ⟨z₁, hs₁, ht₁⟩ := hLift μ₁ hκ₁ hMid₁
  obtain ⟨z₂, hs₂, ht₂⟩ := hLift μ₂ hκ₂ hMid₂
  exact ⟨⟨(z₁, z₂), hs₁.trans hs₂.symm⟩, Prod.ext ht₁ ht₂⟩

#print axioms measure_smoothing_fiber_lift

end BenchmarkJump
