import HellingerMidpoint

open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem sqrt_difference_square_le_abs (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg a)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg b)
    nlinarith

theorem sqrt_convex_smoothing_square_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Real.sqrt ((1 - t) * a + t * b) - Real.sqrt b) ^ 2 ≤
      (1 - t) * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hmix : 0 ≤ (1 - t) * a + t * b :=
    add_nonneg (mul_nonneg (by linarith) ha) (mul_nonneg ht0 hb)
  have hsz := Real.sq_sqrt hmix
  have hvar : 0 ≤ t * (1 - t) * (Real.sqrt a - Real.sqrt b) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have hsq : ((1 - t) * Real.sqrt a + t * Real.sqrt b) ^ 2 ≤
      (Real.sqrt ((1 - t) * a + t * b)) ^ 2 := by nlinarith
  have hlin : (1 - t) * Real.sqrt a + t * Real.sqrt b ≤
      Real.sqrt ((1 - t) * a + t * b) :=
    (sq_le_sq₀ (add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
      (mul_nonneg ht0 (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)).mp hsq
  have hm := mul_le_mul_of_nonneg_left hlin (Real.sqrt_nonneg b)
  nlinarith

def measureBlend {α : Type*} [MeasurableSpace α] (t : ℝ≥0)
    (μ ν : Measure α) : Measure α := (1 - t) • μ + t • ν

instance measureBlend_isFiniteMeasure {α : Type*} [MeasurableSpace α] (t : ℝ≥0)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (measureBlend t μ ν) := by unfold measureBlend; infer_instance

theorem measureBlend_rnDeriv {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (t : ℝ≥0) (ht : t ≤ 1) :
    ∀ᵐ x ∂ρ, ((measureBlend t μ ν).rnDeriv ρ x).toReal =
      (1 - (t : ℝ)) * (μ.rnDeriv ρ x).toReal + (t : ℝ) * (ν.rnDeriv ρ x).toReal := by
  filter_upwards [Measure.rnDeriv_add ((1 - t) • μ) (t • ν) ρ,
    Measure.rnDeriv_smul_left μ ρ (1 - t), Measure.rnDeriv_smul_left ν ρ t,
    Measure.rnDeriv_ne_top ((1 - t) • μ) ρ, Measure.rnDeriv_ne_top (t • ν) ρ]
    with x ha hμ hν htμ htν
  change (((((1 - t) • μ) + t • ν).rnDeriv ρ x)).toReal = _
  rw [ha]
  simp only [Pi.add_apply, ENNReal.toReal_add htμ htν]
  rw [hμ, hν]
  simp only [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, NNReal.coe_sub ht, NNReal.coe_one]

theorem hellinger_energy_smoothing {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (t : ℝ≥0) (ht : t ≤ 1) :
    MeasureEquivalenceHellinger.energy (measureBlend t μ ν) ν ρ ≤
      (1 - (t : ℝ)) * MeasureEquivalenceHellinger.energy μ ν ρ := by
  unfold MeasureEquivalenceHellinger.energy
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_hellinger_energy (measureBlend t μ ν) ν ρ)
    ((integrable_hellinger_energy μ ν ρ).const_mul _)
  filter_upwards [measureBlend_rnDeriv μ ν ρ t ht] with x hx
  rw [hx]
  exact sqrt_convex_smoothing_square_bound _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    t.property (NNReal.coe_le_coe.mpr ht)

theorem integrable_toReal_rnDeriv_finite {α : Type*} [MeasurableSpace α]
    (μ ρ : Measure α) [IsFiniteMeasure μ] : Integrable (fun x => (μ.rnDeriv ρ x).toReal) ρ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    Measure.integrableOn_toReal_rnDeriv (ν := ρ) (measure_ne_top μ univ)

/-- Along the actual convex segment between arbitrary probability measures,
squared Hellinger distance is at most twice the difference of parameters. -/
theorem hellinger_energy_blend_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t u : ℝ≥0) (ht : t ≤ 1) (hu : u ≤ 1) :
    MeasureEquivalenceHellinger.energy (measureBlend t μ ν) (measureBlend u μ ν) (μ + ν) ≤
      2 * |(t : ℝ) - (u : ℝ)| := by
  have hIμ := integrable_toReal_rnDeriv_finite μ (μ + ν)
  have hIν := integrable_toReal_rnDeriv_finite ν (μ + ν)
  have hμac : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνac : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hI := (hIμ.add hIν).const_mul |(t : ℝ) - (u : ℝ)|
  have hBound : MeasureEquivalenceHellinger.energy (measureBlend t μ ν) (measureBlend u μ ν) (μ + ν) ≤
      ∫ x, |(t : ℝ) - (u : ℝ)| *
        ((μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν) := by
    apply integral_mono_ae (integrable_hellinger_energy _ _ _) hI
    filter_upwards [measureBlend_rnDeriv μ ν (μ + ν) t ht,
      measureBlend_rnDeriv μ ν (μ + ν) u hu] with x htx hux
    calc
      _ ≤ |((measureBlend t μ ν).rnDeriv (μ + ν) x).toReal -
          ((measureBlend u μ ν).rnDeriv (μ + ν) x).toReal| :=
        sqrt_difference_square_le_abs _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      _ = |(t : ℝ) - (u : ℝ)| *
          |(ν.rnDeriv (μ + ν) x).toReal - (μ.rnDeriv (μ + ν) x).toReal| := by
        rw [htx, hux, ← abs_mul]
        congr 1
        ring
      _ ≤ |(t : ℝ) - (u : ℝ)| *
          ((μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith only [
          (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv (μ + ν) x).toReal),
          (ENNReal.toReal_nonneg : 0 ≤ (ν.rnDeriv (μ + ν) x).toReal)]
  calc
    _ ≤ _ := hBound
    _ = |(t : ℝ) - (u : ℝ)| * (μ.real univ + ν.real univ) := by
      rw [integral_const_mul, integral_add hIμ hIν,
        Measure.integral_toReal_rnDeriv hμac, Measure.integral_toReal_rnDeriv hνac]
    _ = _ := by simp only [measureReal_def, measure_univ, ENNReal.toReal_one]; ring

#print axioms hellinger_energy_smoothing
#print axioms hellinger_energy_blend_le

end BenchmarkJump
