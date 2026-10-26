import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def exponentialDensity (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-t))
def exponentialMeasure : Measure ℝ := volume.withDensity exponentialDensity
def baseInterval : Set ℝ := Icc (-Real.log 2) 0
def baseMeasure : Measure ℝ := exponentialMeasure.restrict baseInterval

theorem measurable_exponentialDensity : Measurable exponentialDensity :=
  (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal

instance : SigmaFinite exponentialMeasure := by
  unfold exponentialMeasure exponentialDensity
  infer_instance

theorem exponentialMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    exponentialMeasure s = ∫⁻ t in s, exponentialDensity t :=
  withDensity_apply _ hs

theorem exponentialDensity_shift (a t : ℝ) :
    exponentialDensity (t - a) = ENNReal.ofReal (Real.exp a) * exponentialDensity t := by
  dsimp [exponentialDensity]
  rw [show -(t - a) = a + -t by ring, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg a)]

theorem map_add_exponentialMeasure (a : ℝ) :
    exponentialMeasure.map (fun t => t + a) =
      ENNReal.ofReal (Real.exp a) • exponentialMeasure := by
  have hm : Measurable (fun t : ℝ => t + a) := measurable_id.add_const a
  have hp : MeasurePreserving (fun t : ℝ => t + a) volume volume :=
    measurePreserving_add_right volume a
  ext s hs
  rw [Measure.map_apply hm hs, exponentialMeasure_apply (hm hs), Measure.smul_apply,
    exponentialMeasure_apply hs, smul_eq_mul]
  calc
    (∫⁻ t in (fun t : ℝ => t + a) ⁻¹' s, exponentialDensity t) =
        ∫⁻ t in (fun t : ℝ => t + a) ⁻¹' s, exponentialDensity ((t + a) - a) := by simp
    _ = ∫⁻ t in s, exponentialDensity (t - a) :=
      hp.setLIntegral_comp_preimage hs (measurable_exponentialDensity.comp (measurable_id.sub_const a))
    _ = ENNReal.ofReal (Real.exp a) * ∫⁻ t in s, exponentialDensity t := by
      simp_rw [exponentialDensity_shift]
      exact lintegral_const_mul _ measurable_exponentialDensity

theorem integral_baseInterval : (∫ t in baseInterval, Real.exp (-t)) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [baseInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_nonpos.mpr hlog),
    intervalIntegral.integral_comp_neg, integral_exp]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem exponentialMeasure_baseInterval : exponentialMeasure baseInterval = 1 := by
  rw [exponentialMeasure_apply (show MeasurableSet baseInterval from measurableSet_Icc)]
  dsimp only [exponentialDensity]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_baseInterval]
    norm_num
  · exact (Real.continuous_exp.comp continuous_neg).integrableOn_Icc
  · exact ae_of_all _ (fun t => Real.exp_nonneg _)

instance : IsProbabilityMeasure baseMeasure := by
  constructor
  rw [baseMeasure, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    exponentialMeasure_baseInterval]

instance : NoAtoms exponentialMeasure := by
  unfold exponentialMeasure
  infer_instance

instance : NoAtoms baseMeasure := by
  unfold baseMeasure
  infer_instance

theorem exponentialMeasure_univ : exponentialMeasure univ = ∞ := by
  by_contra hfin
  have hpos : exponentialMeasure univ ≠ 0 := by
    have hle : (1 : ℝ≥0∞) ≤ exponentialMeasure univ := by
      rw [← exponentialMeasure_baseInterval]
      exact measure_mono (subset_univ _)
    exact ne_of_gt (zero_lt_one.trans_le hle)
  have he := congrArg (fun μ : Measure ℝ => μ univ) (map_add_exponentialMeasure 1)
  dsimp only at he
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at he
  simp only [preimage_univ, Measure.smul_apply, smul_eq_mul] at he
  have hc : ENNReal.ofReal (Real.exp 1) = 1 :=
    (ENNReal.mul_eq_right hpos hfin).mp he.symm
  have hr := congrArg ENNReal.toReal hc
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_one] at hr
  exact (ne_of_gt (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1))) hr

#print axioms map_add_exponentialMeasure
#print axioms exponentialMeasure_baseInterval
#print axioms exponentialMeasure_univ

end MeasureEquivalenceRestrictedProduct
