import RestrictedSpectralClass

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid

theorem sequenceEmbedding_measurableEmbedding : MeasurableEmbedding sequenceEmbedding :=
  sequenceEmbedding_continuous.measurableEmbedding sequenceEmbedding_injective

def compactMeasure : Measure CompactSequences := restrictedProductMeasure.map sequenceEmbedding

instance : SigmaFinite compactMeasure := sequenceEmbedding_measurableEmbedding.sigmaFinite_map

theorem compactMeasure_translate_real (h : RealSequences) :
    compactMeasure.map (fun z => z + sequenceEmbedding h) =
      (restrictedProductMeasure.map (fun x => x + h)).map sequenceEmbedding := by
  rw [compactMeasure, Measure.map_map (by fun_prop) sequenceEmbedding_continuous.measurable,
    Measure.map_map sequenceEmbedding_continuous.measurable (by fun_prop)]
  congr 1
  funext x
  exact (map_add sequenceEmbedding x h).symm

theorem compactMeasure_summable_modulus (h : RealSequences)
    (hs : Summable (fun n => |h n|)) :
    compactMeasure.map (fun z => z + sequenceEmbedding h) =
      ENNReal.ofReal (Real.exp (∑' n, h n)) • compactMeasure := by
  rw [compactMeasure_translate_real, map_summable_restrictedProductMeasure h hs,
    Measure.map_smul, compactMeasure]

theorem compactMeasure_not_summable_singular (h : RealSequences)
    (hs : ¬ Summable (fun n => |h n|)) :
    compactMeasure.map (fun z => z + sequenceEmbedding h) ⟂ₘ compactMeasure := by
  rw [compactMeasure_translate_real]
  exact sequenceEmbedding_measurableEmbedding.mutuallySingular_map
    (map_shift_mutuallySingular_of_not_summable h hs)

theorem compactMeasure_outside_real_range_singular (k : CompactSequences)
    (hk : k ∉ range sequenceEmbedding) :
    compactMeasure.map (fun z => z + k) ⟂ₘ compactMeasure := by
  let R := range sequenceEmbedding
  have hR : MeasurableSet R := sequenceEmbedding_measurableEmbedding.measurableSet_range
  refine ⟨R, hR, ?_, ?_⟩
  · rw [Measure.map_apply (by fun_prop) hR, compactMeasure,
      Measure.map_apply sequenceEmbedding_continuous.measurable ((by fun_prop :
        Measurable (fun z : CompactSequences => z + k)) hR)]
    have he : sequenceEmbedding ⁻¹' ((fun z : CompactSequences => z + k) ⁻¹' R) = ∅ := by
      ext x
      simp only [mem_preimage, R, mem_range, mem_empty_iff_false, iff_false]
      rintro ⟨y, hy⟩
      apply hk
      refine ⟨y - x, ?_⟩
      rw [map_sub, hy, add_sub_cancel_left]
    rw [he, measure_empty]
  · rw [compactMeasure, Measure.map_apply sequenceEmbedding_continuous.measurable hR.compl]
    have he : sequenceEmbedding ⁻¹' Rᶜ = ∅ := by ext x; simp [R]
    rw [he, measure_empty]

theorem compactMeasure_outside_summable_singular (k : CompactSequences)
    (hk : k ∉ summableSubgroup) :
    compactMeasure.map (fun z => z + k) ⟂ₘ compactMeasure := by
  by_cases hR : k ∈ range sequenceEmbedding
  · obtain ⟨h, rfl⟩ := hR
    apply compactMeasure_not_summable_singular
    intro hs
    have hm : Memℓp h 1 := by
      apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)).2
      simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using hs
    exact hk ⟨⟨h, hm⟩, rfl⟩
  · exact compactMeasure_outside_real_range_singular k hR

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.compactMeasure_summable_modulus
#print axioms MeasureEquivalenceRestrictedPhase.compactMeasure_outside_summable_singular
