import HellingerTransport

/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Y : Type*} [MeasurableSpace Y]

/-- Hellinger affinity, using the canonical dominating measure `μ + ν`. -/
noncomputable def affinity (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  inner ℝ (root μ (μ + ν)) (root ν (μ + ν))

/-- The same RN integral with an explicit dominating reference measure. -/
noncomputable def affinityAgainst (μ ν ρ : Measure Y) : ℝ :=
  ∫ y, Real.sqrt (μ.rnDeriv ρ y).toReal * Real.sqrt (ν.rnDeriv ρ y).toReal ∂ρ

theorem affinity_integral (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    affinity μ ν = ∫ y, Real.sqrt (μ.rnDeriv (μ + ν) y).toReal *
      Real.sqrt (ν.rnDeriv (μ + ν) y).toReal ∂(μ + ν) := by
  rw [affinity, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [root_coe μ (μ + ν), root_coe ν (μ + ν)] with y hμ hν
  rw [hμ, hν]
  simp [mul_comm]

theorem integrable_affinity_integrand (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun y => Real.sqrt (μ.rnDeriv (μ + ν) y).toReal *
      Real.sqrt (ν.rnDeriv (μ + ν) y).toReal) (μ + ν) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (root μ (μ + ν)) (root ν (μ + ν))).congr
  filter_upwards [root_coe μ (μ + ν), root_coe ν (μ + ν)] with y hμ hν
  rw [hμ, hν]
  simp [mul_comm]

theorem affinity_nonneg (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ affinity μ ν := by
  rw [affinity_integral]
  apply integral_nonneg
  intro y
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Change of dominating measure for the actual affinity RN integral. -/
theorem affinityAgainst_change_reference (μ ν ρ σ : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    affinityAgainst μ ν σ = affinityAgainst μ ν ρ := by
  unfold affinityAgainst
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with y hmy hny
  simp only [Pi.mul_apply] at hmy hny
  rw [← hmy, ← hny, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_mul ENNReal.toReal_nonneg]
  calc
    _ = (Real.sqrt (ρ.rnDeriv σ y).toReal) ^ 2 *
        (Real.sqrt (μ.rnDeriv ρ y).toReal * Real.sqrt (ν.rnDeriv ρ y).toReal) := by ring
    _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]

/-- Any sigma-finite common dominating measure computes the same affinity. -/
theorem affinity_eq_affinityAgainst (μ ν ρ : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    affinity μ ν = affinityAgainst μ ν ρ := by
  rw [affinity_integral]
  change affinityAgainst μ ν (μ + ν) = affinityAgainst μ ν ρ
  exact (affinityAgainst_change_reference μ ν (μ + ν) ρ
    (Measure.AbsolutelyContinuous.rfl.add_right ν)
    (Measure.AbsolutelyContinuous.rfl.add_right' μ)
    (Measure.AbsolutelyContinuous.add_left hμ hν)).symm

theorem affinity_le_one (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : affinity μ ν ≤ 1 := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  calc
    affinity μ ν ≤ ‖root μ (μ + ν)‖ * ‖root ν (μ + ν)‖ := real_inner_le_norm _ _
    _ = 1 := by rw [root_probability_norm μ _ hμ, root_probability_norm ν _ hν, mul_one]

/-- Zero affinity is precisely disjointness of the measure classes. -/
theorem affinity_eq_zero_iff_mutuallySingular (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : affinity μ ν = 0 ↔ μ ⟂ₘ ν := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  constructor
  · intro ha
    rw [affinity_integral] at ha
    have haz := (integral_eq_zero_iff_of_nonneg
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (integrable_affinity_integrand μ ν)).mp ha
    have hprod : ∀ᵐ y ∂(μ + ν),
        μ.rnDeriv (μ + ν) y = 0 ∨ ν.rnDeriv (μ + ν) y = 0 := by
      filter_upwards [haz, Measure.rnDeriv_ne_top μ (μ + ν),
        Measure.rnDeriv_ne_top ν (μ + ν)] with y hy hμt hνt
      rcases mul_eq_zero.mp hy with h | h
      · left
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          ((Real.sqrt_eq_zero ENNReal.toReal_nonneg).mp h)).resolve_right hμt
      · right
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          ((Real.sqrt_eq_zero ENNReal.toReal_nonneg).mp h)).resolve_right hνt
    let s : Set Y := {y | μ.rnDeriv (μ + ν) y = 0}
    have hsm : MeasurableSet s := (Measure.measurable_rnDeriv _ _) (measurableSet_singleton 0)
    have hμs : μ s = 0 := by
      rw [← Measure.withDensity_rnDeriv_eq μ (μ + ν) hμ,
        withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
      have hempty : {y | μ.rnDeriv (μ + ν) y ≠ 0} ∩ s = ∅ := by
        ext y
        simp [s]
      rw [hempty, measure_empty]
    have hνsc : ν sᶜ = 0 := by
      rw [← Measure.withDensity_rnDeriv_eq ν (μ + ν) hν,
        withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
      have hset : {x | ν.rnDeriv (μ + ν) x ≠ 0} ∩ sᶜ =
          {x | ¬ (μ.rnDeriv (μ + ν) x = 0 ∨ ν.rnDeriv (μ + ν) x = 0)} := by
        ext y
        simp [s, and_comm]
      rw [hset]
      exact ae_iff.mp hprod
    exact ⟨s, hsm, hμs, hνsc⟩
  · intro hs
    rw [affinity_integral]
    apply integral_eq_zero_of_ae
    apply ae_add_measure_iff.mpr
    constructor
    · filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular hs.symm hμ] with y hy
      simp [hy]
    · filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular hs hν] with y hy
      simp [hy]

/-- A nonzero probability absolutely continuous with respect to another
probability has strictly positive Hellinger affinity. -/
theorem affinity_pos_of_absolutelyContinuous (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) : 0 < affinity μ ν := by
  apply lt_of_le_of_ne (affinity_nonneg μ ν)
  intro hzero
  have hsing := (affinity_eq_zero_iff_mutuallySingular μ ν).mp hzero.symm
  have hμzero := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hμν hsing
  have hm := congrArg (fun ρ : Measure Y => ρ Set.univ) hμzero
  simp at hm

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.affinity_nonneg
#print axioms MeasureEquivalenceHellinger.affinity_le_one
#print axioms MeasureEquivalenceHellinger.affinity_eq_zero_iff_mutuallySingular
#print axioms MeasureEquivalenceHellinger.affinityAgainst_change_reference
#print axioms MeasureEquivalenceHellinger.affinity_eq_affinityAgainst
#print axioms MeasureEquivalenceHellinger.affinity_pos_of_absolutelyContinuous
