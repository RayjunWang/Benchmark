import HellingerAffinity

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z]

theorem affinity_eq_inner_roots (μ ν ρ : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    affinity μ ν = inner ℝ (root μ ρ) (root ν ρ) := by
  rw [affinity_eq_affinityAgainst μ ν ρ hμ hν, affinityAgainst, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [root_coe μ ρ, root_coe ν ρ] with z hμz hνz
  rw [hμz, hνz]
  simp [mul_comm]

@[simp] theorem affinity_self (μ : Measure Z) [IsProbabilityMeasure μ] : affinity μ μ = 1 := by
  rw [affinity_eq_inner_roots μ μ μ Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl,
    real_inner_self_eq_norm_sq, root_probability_norm μ μ Measure.AbsolutelyContinuous.rfl]
  norm_num

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.affinity_eq_inner_roots
