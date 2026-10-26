import HellingerTransport

/-! Concrete Hellinger midpoint estimates for the measure-jump proof. -/

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem sqrt_midpoint_square_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt ((a + b) / 2)) ^ 2 ≤
      (1 / 2 : ℝ) * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  have hz := Real.sq_sqrt (show 0 ≤ (a + b) / 2 by positivity)
  have hs : (Real.sqrt a + Real.sqrt b) ^ 2 ≤
      (2 * Real.sqrt ((a + b) / 2)) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
  have hlinear : Real.sqrt a + Real.sqrt b ≤ 2 * Real.sqrt ((a + b) / 2) :=
    (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by positivity)).mp hs
  have hmul := mul_le_mul_of_nonneg_left hlinear (Real.sqrt_nonneg a)
  nlinarith

theorem integrable_hellinger_energy {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x =>
      (Real.sqrt (μ.rnDeriv ρ x).toReal - Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2) ρ := by
  have hmem := (MeasureEquivalenceHellinger.sqrt_rnDeriv_memLp μ ρ).sub
    (MeasureEquivalenceHellinger.sqrt_rnDeriv_memLp ν ρ)
  exact (memLp_two_iff_integrable_sq
    (((Measure.measurable_rnDeriv μ ρ).ennreal_toReal.sqrt.sub
      (Measure.measurable_rnDeriv ν ρ).ennreal_toReal.sqrt).aestronglyMeasurable)).mp hmem

def measureMidpoint {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : Measure α :=
  (1 / 2 : ℝ≥0) • (μ + ν)

/-- The actual midpoint measure contracts squared Hellinger distance to
either endpoint by a factor of at least one half, with a common reference. -/
theorem hellinger_energy_midpoint {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ] :
    MeasureEquivalenceHellinger.energy μ (measureMidpoint μ ν) ρ ≤
      (1 / 2 : ℝ) * MeasureEquivalenceHellinger.energy μ ν ρ := by
  letI : IsFiniteMeasure (measureMidpoint μ ν) := by
    unfold measureMidpoint
    infer_instance
  have hRN : ∀ᵐ x ∂ρ,
      ((measureMidpoint μ ν).rnDeriv ρ x).toReal =
        ((μ.rnDeriv ρ x).toReal + (ν.rnDeriv ρ x).toReal) / 2 := by
    filter_upwards [Measure.rnDeriv_smul_left (μ + ν) ρ (1 / 2 : ℝ≥0),
      Measure.rnDeriv_add μ ν ρ, Measure.rnDeriv_ne_top μ ρ, Measure.rnDeriv_ne_top ν ρ]
      with x hs ha hμ hν
    change ((measureMidpoint μ ν).rnDeriv ρ x) =
      (1 / 2 : ℝ≥0) • (μ + ν).rnDeriv ρ x at hs
    rw [hs, ha]
    simp only [Pi.add_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add hμ hν]
    norm_num
    ring
  unfold MeasureEquivalenceHellinger.energy
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_hellinger_energy μ (measureMidpoint μ ν) ρ)
    ((integrable_hellinger_energy μ ν ρ).const_mul (1 / 2 : ℝ))
  filter_upwards [hRN] with x hx
  rw [hx]
  exact sqrt_midpoint_square_bound _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg

#print axioms hellinger_energy_midpoint

end BenchmarkJump
