import RestrictedDensity
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

variable {ι : Type*} [Fintype ι]

def expNNReal (a : ℝ) : ℝ≥0 := ⟨Real.exp a, Real.exp_nonneg a⟩

@[simp] theorem coe_expNNReal (a : ℝ) :
    (expNNReal a : ℝ≥0∞) = ENNReal.ofReal (Real.exp a) := by
  rw [ENNReal.ofReal]
  congr 1
  apply NNReal.coe_injective
  simp [expNNReal, Real.toNNReal_of_nonneg (Real.exp_nonneg a)]
  rfl

theorem pi_smul_nnreal {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    (Measure.pi fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finsetProd,
    Finset.prod_mul_distrib]

theorem map_add_exponentialMeasure_nnreal (a : ℝ) :
    exponentialMeasure.map (fun t => t + a) = expNNReal a • exponentialMeasure := by
  rw [map_add_exponentialMeasure]
  ext s hs
  simp [Measure.smul_apply, smul_eq_mul]

theorem pi_map_add_exponentialMeasure (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => exponentialMeasure)).map (fun x i => x i + a i) =
      (expNNReal (∑ i, a i)) • Measure.pi (fun _ : ι => exponentialMeasure) := by
  letI (i : ι) : SigmaFinite (exponentialMeasure.map (fun t => t + a i)) := by
    rw [map_add_exponentialMeasure_nnreal]
    infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : ι => exponentialMeasure)
    (f := fun i t => t + a i) (fun i => (measurable_id.add_const (a i)).aemeasurable)
  dsimp only [id_eq] at hmap
  rw [hmap]
  simp_rw [map_add_exponentialMeasure_nnreal]
  rw [pi_smul_nnreal]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_prod, expNNReal, Real.exp_sum]
  rfl

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.pi_map_add_exponentialMeasure
