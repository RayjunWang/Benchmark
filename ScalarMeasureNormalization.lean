import MeasureUnitaryRN

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]

theorem scalar_smul_absolutelyContinuous (c : ℝ≥0) : c • μ ≪ μ := by
  change (c : ℝ≥0∞) • μ ≪ μ
  exact Measure.smul_absolutelyContinuous

theorem scalar_absolutelyContinuous_smul (c : ℝ≥0) (hc : c ≠ 0) : μ ≪ c • μ := by
  change μ ≪ (c : ℝ≥0∞) • μ
  exact Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr hc)

def scalarMeasureEquiv (c : ℝ≥0) (hc : c ≠ 0) :
    Lp ℂ 2 (c • μ) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  rnWeightedEquiv (c • μ) μ (scalar_smul_absolutelyContinuous μ c)
    (scalar_absolutelyContinuous_smul μ c hc)

theorem scalar_rnWeight (c : ℝ≥0) :
    rnWeight (c • μ) μ =ᵐ[μ] fun _ => Real.sqrt (c : ℝ) := by
  filter_upwards [Measure.rnDeriv_smul_left' μ μ c, μ.rnDeriv_self] with x hx hself
  unfold rnWeight
  rw [hx]
  change Real.sqrt (((c : ℝ≥0∞) * μ.rnDeriv μ x).toReal) = _
  rw [hself]
  simp

theorem scalarMeasureEquiv_coe (c : ℝ≥0) (hc : c ≠ 0) (f : Lp ℂ 2 (c • μ)) :
    scalarMeasureEquiv μ c hc f =ᵐ[μ] fun x => Real.sqrt (c : ℝ) • f x := by
  change rnWeightedMap (c • μ) μ (scalar_smul_absolutelyContinuous μ c)
    (scalar_absolutelyContinuous_smul μ c hc) f =ᵐ[μ] _
  filter_upwards [rnWeightedMap_coe (c • μ) μ (scalar_smul_absolutelyContinuous μ c)
    (scalar_absolutelyContinuous_smul μ c hc) f, scalar_rnWeight μ c] with x hx hw
  rw [hx, hw]

theorem scalarMeasureEquiv_symm_coe (c : ℝ≥0) (hc : c ≠ 0) (f : Lp ℂ 2 μ) :
    (scalarMeasureEquiv μ c hc).symm f =ᵐ[c • μ]
      fun x => (Real.sqrt (c : ℝ))⁻¹ • f x := by
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
  have hsqrt : Real.sqrt (c : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcpos)
  have he := scalarMeasureEquiv_coe μ c hc ((scalarMeasureEquiv μ c hc).symm f)
  simp only [LinearIsometryEquiv.apply_symm_apply] at he
  refine Measure.ae_smul_measure ?_ c
  filter_upwards [he] with x hx
  have hh := congrArg (fun z : ℂ => (Real.sqrt (c : ℝ))⁻¹ • z) hx
  simpa only [smul_smul, inv_mul_cancel₀ hsqrt, one_smul] using hh.symm

end MeasureUnitary

#print axioms MeasureUnitary.scalarMeasureEquiv
#print axioms MeasureUnitary.scalarMeasureEquiv_coe
#print axioms MeasureUnitary.scalarMeasureEquiv_symm_coe
