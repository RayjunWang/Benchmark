import MeasureClassClosedCover
import CantorPrefixPerturbation
import CantorProbabilityMix
import Mathlib.Topology.GDelta.Basic

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

set_option maxHeartbeats 1500000

namespace BenchmarkJump

theorem exists_small_mixing_parameter (ε : ℝ≥0∞) (hε : ε ≠ 0) (hε1 : ε ≤ 1) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ ENNReal.ofReal (t : ℝ) < ε := by
  obtain ⟨r,hr,hrε⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 1) (b := ε) (by simp) hε
  simp only [mul_one] at hrε
  have hr1 : r ≤ 1 := by exact_mod_cast hrε.le.trans hε1
  refine ⟨⟨(r : ℝ), r.coe_nonneg, by exact_mod_cast hr1⟩, by exact_mod_cast hr, ?_⟩
  simpa using hrε

theorem redirectedProbability_compl_small (μ ν : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    (redirectedProbability μ ν n m : Measure HaarCantor) (smallPrefixRegion μ n m)ᶜ = 0 := by
  rw [show (redirectedProbability μ ν n m : Measure HaarCantor) =
      (ν : Measure HaarCantor).map (prefixRedirect μ n m) from rfl,
    Measure.map_apply (continuous_prefixRedirect μ n m).measurable
      (smallPrefixRegion_clopen μ n m).isClosed.measurableSet.compl]
  have he : prefixRedirect μ n m ⁻¹' (smallPrefixRegion μ n m)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx (prefixRedirect_mem_smallPrefixRegion μ n m x)
  rw [he,measure_empty]

theorem smallPrefixRegion_compl_large (μ : ProbabilityMeasure HaarCantor) (n : ℕ) :
    (2⁻¹ : ℝ≥0∞) ≤ (μ : Measure HaarCantor) (smallPrefixRegion μ n 2)ᶜ := by
  have hsmall := smallPrefixRegion_mass_bound μ n 2
  have hsum := measureReal_add_measureReal_compl (μ := (μ : Measure HaarCantor))
    (smallPrefixRegion_clopen μ n 2).isClosed.measurableSet
  have hr : (1 / 2 : ℝ) ≤ (μ : Measure HaarCantor).real (smallPrefixRegion μ n 2)ᶜ := by
    norm_num at hsmall hsum ⊢
    linarith
  apply (ENNReal.toReal_le_toReal (by simp) (measure_ne_top _ _)).mp
  simpa using hr

theorem fullSupport_redirected_tendsto (μ : ProbabilityMeasure HaarCantor)
    (ν : PositiveCylinderProbabilities) (t : unitInterval) (ht : 0 < (t : ℝ)) :
    Tendsto (fun n => fullSupportMix t ht (redirectedProbability μ ν n 2) ν) atTop (𝓝 ν) := by
  have h : Tendsto (fun p : ProbabilityMeasure HaarCantor × PositiveCylinderProbabilities =>
      fullSupportMix t ht p.1 p.2) (𝓝 ((ν : ProbabilityMeasure HaarCantor),ν))
      (𝓝 (fullSupportMix t ht (ν : ProbabilityMeasure HaarCantor) ν)) :=
    (continuous_fullSupportMix t ht).tendsto ((ν : ProbabilityMeasure HaarCantor),ν)
  have hp : Tendsto (fun n => (redirectedProbability μ ν n 2,ν)) atTop
      (𝓝 ((ν : ProbabilityMeasure HaarCantor),ν)) :=
    (redirectedProbability_tendsto μ ν 2).prodMk_nhds (tendsto_const_nhds (x := ν))
  have he : fullSupportMix t ht (ν : ProbabilityMeasure HaarCantor) ν = ν :=
    Subtype.ext (cantorProbabilityMix_self t ν)
  simpa only [he] using h.comp hp

theorem fullSupport_redirected_outside (μ : ProbabilityMeasure HaarCantor)
    (ν : PositiveCylinderProbabilities) (k : ℕ) (t : unitInterval) (ht : 0 < (t : ℝ))
    (htsmall : ENNReal.ofReal (t : ℝ) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) (n : ℕ) :
    fullSupportMix t ht (redirectedProbability μ ν n 2) ν ∉ clopenACBound μ k := by
  intro h
  let A := (smallPrefixRegion μ n 2)ᶜ
  have hA : IsClopen A := (smallPrefixRegion_clopen μ n 2).compl
  have hlower := h A hA (smallPrefixRegion_compl_large μ n)
  have hupper : ((fullSupportMix t ht (redirectedProbability μ ν n 2) ν :
      ProbabilityMeasure HaarCantor) : Measure HaarCantor) A ≤ ENNReal.ofReal (t : ℝ) := by
    change (cantorProbabilityMix t (redirectedProbability μ ν n 2) ν : Measure HaarCantor) A ≤ _
    rw [cantorProbabilityMix_apply, redirectedProbability_compl_small, mul_zero, zero_add]
    have hνA : ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A ≤ 1 := by
      simpa using (measure_mono (subset_univ A) :
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A ≤
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) univ)
    simpa only [mul_one] using mul_le_mul_left' hνA (ENNReal.ofReal (t : ℝ))
  exact (not_lt_of_ge hlower) (hupper.trans_lt htsmall)

theorem isNowhereDense_clopenACBound (μ : ProbabilityMeasure HaarCantor) (k : ℕ) :
    IsNowhereDense (clopenACBound μ k) := by
  apply (isClosed_clopenACBound μ k).isNowhereDense_iff.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro ν hν
  obtain ⟨t,ht,htsmall⟩ := exists_small_mixing_parameter (((k + 1 : ℕ) : ℝ≥0∞)⁻¹)
    (by simp) (ENNReal.inv_le_one.mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)))
  have hlim := fullSupport_redirected_tendsto μ ν t ht
  have hev := hlim.eventually (isOpen_interior.mem_nhds hν)
  obtain ⟨n,hn⟩ := hev.exists
  exact fullSupport_redirected_outside μ ν k t ht htsmall n (interior_subset hn)

theorem measure_ac_class_meagre (μ : ProbabilityMeasure HaarCantor) :
    IsMeagre {ν : PositiveCylinderProbabilities |
      (μ : Measure HaarCantor) ≪ ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)} := by
  apply (isMeagre_iUnion (fun k => (isNowhereDense_clopenACBound μ k).isMeagre)).mono
  intro ν hν
  obtain ⟨k,hk⟩ := ac_mem_clopenACBound μ ν hν
  exact mem_iUnion.mpr ⟨k,hk⟩

theorem measure_equivalence_class_meagre (μ : PositiveCylinderProbabilities) :
    IsMeagre {ν : PositiveCylinderProbabilities |
      (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ∧
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
          ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))} :=
  (measure_ac_class_meagre μ).mono (fun _ h => h.1)

end BenchmarkJump

#print axioms BenchmarkJump.measure_equivalence_class_meagre
