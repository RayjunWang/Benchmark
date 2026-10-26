import HellingerAffinity

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace BenchmarkJump

variable {Y : Type*} [MeasurableSpace Y]

def weightedAffinityAgainst (g : Y → ℝ) (μ ν ρ : Measure Y) : ℝ :=
  ∫ x, g x * (Real.sqrt (μ.rnDeriv ρ x).toReal *
    Real.sqrt (ν.rnDeriv ρ x).toReal) ∂ρ

theorem weightedAffinityAgainst_change_reference (g : Y → ℝ) (μ ν ρ σ : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    weightedAffinityAgainst g μ ν σ = weightedAffinityAgainst g μ ν ρ := by
  unfold weightedAffinityAgainst
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with x hmx hnx
  simp only [Pi.mul_apply] at hmx hnx
  rw [← hmx, ← hnx, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_mul ENNReal.toReal_nonneg]
  calc
    _ = g x * (Real.sqrt (ρ.rnDeriv σ x).toReal) ^ 2 *
        (Real.sqrt (μ.rnDeriv ρ x).toReal * Real.sqrt (ν.rnDeriv ρ x).toReal) := by ring
    _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]; ring

/-- Change of orientation of a weighted square-root density integral.
This is an actual RN change-of-measure identity. -/
theorem weighted_root_switch (g : Y → ℝ) (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (∫ x, g x * MeasureEquivalenceHellinger.root μ ν x ∂ν) =
      ∫ x, g x * MeasureEquivalenceHellinger.root ν μ x ∂μ := by
  have hν : weightedAffinityAgainst g μ ν ν =
      ∫ x, g x * MeasureEquivalenceHellinger.root μ ν x ∂ν := by
    unfold weightedAffinityAgainst
    apply integral_congr_ae
    filter_upwards [Measure.rnDeriv_self ν,
      MeasureEquivalenceHellinger.root_coe μ ν] with x hself hr
    rw [hself, ENNReal.toReal_one, Real.sqrt_one, mul_one, hr]
  have hμ : weightedAffinityAgainst g μ ν μ =
      ∫ x, g x * MeasureEquivalenceHellinger.root ν μ x ∂μ := by
    unfold weightedAffinityAgainst
    apply integral_congr_ae
    filter_upwards [Measure.rnDeriv_self μ,
      MeasureEquivalenceHellinger.root_coe ν μ] with x hself hr
    rw [hself, ENNReal.toReal_one, Real.sqrt_one, one_mul, hr]
  rw [← hν, ← hμ]
  exact (weightedAffinityAgainst_change_reference g μ ν ν μ hμν
    Measure.AbsolutelyContinuous.rfl hνμ).symm

#print axioms weighted_root_switch

end BenchmarkJump
