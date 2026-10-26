import RestrictedTranslatedCorner

/-! A scalar-normalized translation intertwines the actual phase and
index-shift generators on the translated corner. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

abbrev TranslatedHilbert (h : RealSequences) :=
  Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h))

theorem translatedCorner_ambientPhase (h : RealSequences) (k : CompactSequences)
    (i : CharacterIndex) (p : RealSequences × RationalGroup) :
    ambientPhase k i (orbitPoint (translatedCornerEquiv h p)) =
      ambientPhase (k + sequenceEmbedding h) i (orbitPoint p) := by
  change character i (k + sequenceEmbedding (p.1 + h +
    rationalRealShift (Multiplicative.toAdd p.2 : rationalZeroSumGroup))) =
    character i (k + sequenceEmbedding h + sequenceEmbedding (p.1 +
      rationalRealShift (Multiplicative.toAdd p.2 : rationalZeroSumGroup)))
  simp only [map_add]
  congr 1
  abel

theorem normalizedTranslation_phase_intertwines (h : RealSequences)
    (hs : Summable (fun n => |h n|))
    (V : InducedHilbert ≃ₗᵢ[ℂ] TranslatedHilbert h) (a : ℝ)
    (hV : ∀ u : InducedHilbert,
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
        fun p => a • u (translatedCornerEquiv h p))
    (k : CompactSequences) (i : CharacterIndex) (u : InducedHilbert) :
    V (inducedFamilyPhase k i u) =
      inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
        (ambientPhase (k + sequenceEmbedding h) i) (ambientPhase_measurable _ _)
          (ambientPhase_norm _ _) (V u) := by
  apply Lp.ext
  filter_upwards [hV (inducedFamilyPhase k i u),
    (translatedCorner_quasiMeasurePreserving h hs).ae
      (inducedPhaseUnitary_coe restrictedProductMeasure (stageSet 0)
        (ambientPhase k i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u),
    inducedPhaseUnitary_coe restrictedProductMeasure (translatedCorner h)
      (ambientPhase (k + sequenceEmbedding h) i) (ambientPhase_measurable _ _)
        (ambientPhase_norm _ _) (V u), hV u] with p hleft hinside hright hVp
  rw [hleft, hright, hVp]
  calc
    a • (inducedFamilyPhase k i u) (translatedCornerEquiv h p) =
        a • (ambientPhase k i (orbitPoint (translatedCornerEquiv h p)) • u (translatedCornerEquiv h p)) :=
      congrArg (fun z : ℂ => a • z) hinside
    _ = _ := by
      rw [translatedCorner_ambientPhase]
      exact smul_comm _ _ _

theorem normalizedTranslation_shift_intertwines (h : RealSequences)
    (hs : Summable (fun n => |h n|))
    (V : InducedHilbert ≃ₗᵢ[ℂ] TranslatedHilbert h) (a : ℝ)
    (hV : ∀ u : InducedHilbert,
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
        fun p => a • u (translatedCornerEquiv h p))
    (g : RationalGroup) (u : InducedHilbert) :
    V (inducedFamilyShift g u) =
      inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g (V u) := by
  apply Lp.ext
  filter_upwards [hV (inducedFamilyShift g u),
    (translatedCorner_quasiMeasurePreserving h hs).ae
      (inducedShiftUnitary_coe restrictedProductMeasure (stageSet 0) g u),
    inducedShiftUnitary_coe restrictedProductMeasure (translatedCorner h) g (V u),
    (indexShift_preserving restrictedProductMeasure (translatedCorner h) g⁻¹).quasiMeasurePreserving.ae (hV u)]
      with p hleft hinside hright hVp
  rw [hleft, hright, hVp]
  exact congrArg (fun z : ℂ => a • z) hinside

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.normalizedTranslation_phase_intertwines
#print axioms MeasureEquivalenceRestrictedPhase.normalizedTranslation_shift_intertwines
