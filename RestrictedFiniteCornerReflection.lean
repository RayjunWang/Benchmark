import RestrictedTranslationIntertwining

/-! The finite-corner mass invariant detects the total of a summable
parameter translation. The normalization unitary is supplied explicitly
with its actual scalar pullback formula. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1500000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

theorem total_eq_zero_of_normalized_intertwiner (h : RealSequences)
    (hs : Summable (fun n => |h n|)) (k l : CompactSequences)
    (he : k + sequenceEmbedding h = l)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u))
    (V : InducedHilbert ≃ₗᵢ[ℂ] TranslatedHilbert h) (a : ℝ)
    (hV : ∀ u : InducedHilbert,
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
        fun p => a • u (translatedCornerEquiv h p)) :
    (∑' n, h n) = 0 := by
  let Q := V.symm.trans W
  have hgen := intertwines_generators_of_intertwines_tuple k l W hW
  have hphase (i : CharacterIndex) (u : InducedHilbert) :
      V (inducedFamilyPhase k i u) =
        inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
          (ambientPhase l i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) (V u) := by
    simpa only [he] using normalizedTranslation_phase_intertwines h hs V a hV k i u
  have hshift (g : RationalGroup) (u : InducedHilbert) :
      V (inducedFamilyShift g u) =
        inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g (V u) :=
    normalizedTranslation_shift_intertwines h hs V a hV g u
  have hQphase (i : CharacterIndex) (f : TranslatedHilbert h) :
      Q (inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
        (ambientPhase l i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) f) =
        inducedFamilyPhase l i (Q f) := by
    have hinv : V.symm (inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
        (ambientPhase l i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) f) =
        inducedFamilyPhase k i (V.symm f) := by
      apply V.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply] using (hphase i (V.symm f)).symm
    change W (V.symm _) = inducedFamilyPhase l i (W (V.symm f))
    rw [hinv, hgen.1]
  have hQshift (g : RationalGroup) (f : TranslatedHilbert h) :
      Q (inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g f) =
        inducedFamilyShift g (Q f) := by
    have hinv : V.symm (inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g f) =
        inducedFamilyShift g (V.symm f) := by
      apply V.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply] using (hshift g (V.symm f)).symm
    change W (V.symm _) = inducedFamilyShift g (W (V.symm f))
    rw [hinv, hgen.2]
  have hfinS : restrictedProductMeasure (stageSet 0) ≠ ∞ := by
    rw [restrictedProductMeasure_base]
    exact ENNReal.one_ne_top
  have hm := induced_corner_character_mass_eq l (translatedCorner h) (stageSet 0)
    (translatedCorner_measurable h) (measurable_stageSet 0) (translatedCorner_finite h hs)
    hfinS Q hQphase hQshift
  exact (translatedCorner_mass_eq_base_iff h hs).mp hm

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.total_eq_zero_of_normalized_intertwiner
