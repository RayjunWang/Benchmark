import InducedCornerUnitary
import MeasureUnitaryDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Actual L2 coefficient operators in a counting-measure coordinate,
with their Fubini square-norm identity. -/

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ]

omit [MeasurableSingletonClass D] in
theorem ae_slice_of_ae {f g : X × D → ℂ}
    (h : f =ᵐ[μ.prod (Measure.count : Measure D)] g) (d : D) :
    (fun x => f (x,d)) =ᵐ[μ] (fun x => g (x,d)) := by
  have hs := (Measure.measurePreserving_swap (μ := (Measure.count : Measure D)) (ν := μ)).quasiMeasurePreserving.ae_eq h
  have ha := Measure.ae_ae_of_ae_prod hs
  exact Measure.ae_count_iff.mp ha d

omit [MeasurableSingletonClass D] in
theorem coefficient_memLp (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) (d : D) :
    MemLp (fun x => u (x,d)) 2 μ := by
  have hI : Integrable (fun p : X × D => ‖u p‖ ^ 2) (μ.prod Measure.count) :=
    (Lp.memLp u).norm.integrable_sq
  have hslice : Integrable (fun x => ‖u (x,d)‖ ^ 2) μ :=
    Measure.ae_count_iff.mp hI.prod_left_ae d
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr hslice
  exact ((Lp.stronglyMeasurable u).comp_measurable
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable

noncomputable def coefficient (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) : Lp ℂ 2 μ :=
  (coefficient_memLp μ u d).toLp (fun x => u (x,d))

omit [MeasurableSingletonClass D] in
theorem coefficient_coe (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    coefficient μ d u =ᵐ[μ] (fun x => u (x,d)) :=
  (coefficient_memLp μ u d).coeFn_toLp

theorem coefficient_norm_sq (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    ‖coefficient μ d u‖ ^ 2 = ∫ x, ‖u (x,d)‖ ^ 2 ∂μ := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  exact (coefficient_coe μ d u).mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)

theorem summable_coefficient_norm_sq (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    Summable (fun d => ‖coefficient μ d u‖ ^ 2) := by
  have hI : Integrable (fun p : X × D => ‖u p‖ ^ 2) (μ.prod Measure.count) :=
    (Lp.memLp u).norm.integrable_sq
  have hs := integrable_count_iff.mp hI.integral_prod_right
  simpa only [← coefficient_norm_sq, Real.norm_eq_abs, abs_sq] using hs

/-- Genuine Fubini/Parseval identity for the actual product L2 space. -/
theorem norm_sq_eq_tsum_coefficient_norm_sq
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    ‖u‖ ^ 2 = ∑' d, ‖coefficient μ d u‖ ^ 2 := by
  have hI : Integrable (fun p : X × D => ‖u p‖ ^ 2) (μ.prod Measure.count) :=
    (Lp.memLp u).norm.integrable_sq
  rw [l2_norm_sq_integral, integral_prod_symm _ hI,
    integral_countable hI.integral_prod_right]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    ← coefficient_norm_sq]

theorem coefficient_norm_le (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    ‖coefficient μ d u‖ ≤ ‖u‖ := by
  have hsum := summable_coefficient_norm_sq μ u
  have hle : ‖coefficient μ d u‖ ^ 2 ≤ ∑' i, ‖coefficient μ i u‖ ^ 2 :=
    hsum.le_tsum d (fun _ _ => sq_nonneg _)
  rw [← norm_sq_eq_tsum_coefficient_norm_sq] at hle
  nlinarith [norm_nonneg (coefficient μ d u), norm_nonneg u]

noncomputable def coefficientCLM (d : D) :
    Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := coefficient μ d
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [coefficient_coe μ d (u+v), coefficient_coe μ d u,
          coefficient_coe μ d v, Lp.coeFn_add (coefficient μ d u) (coefficient μ d v),
          ae_slice_of_ae μ (Lp.coeFn_add u v) d] with x huv hu hv hsum hsource
        simp only [Pi.add_apply] at hsum hsource
        rw [huv, hsum, hu, hv, hsource]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [coefficient_coe μ d (c • u), coefficient_coe μ d u,
          Lp.coeFn_smul c (coefficient μ d u), ae_slice_of_ae μ (Lp.coeFn_smul c u) d]
          with x hcu hu hsmul hsource
        simp only [Pi.smul_apply] at hsmul hsource
        simp only [RingHom.id_apply]
        rw [hcu, hsmul, hu, hsource] }
    1 (fun u => by simpa only [one_mul] using coefficient_norm_le μ d u)

end MeasureEquivalenceL2Coefficients

#print axioms MeasureEquivalenceL2Coefficients.norm_sq_eq_tsum_coefficient_norm_sq
#print axioms MeasureEquivalenceL2Coefficients.coefficientCLM
