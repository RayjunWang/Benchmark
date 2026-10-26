import RestrictedCornerCharacterMass

/-! The exact translated finite corner and the measure-preserving map
to the scalar multiple dictated by the restricted-product modulus. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition

def translationScale (h : RealSequences) : ℝ≥0 :=
  ⟨Real.exp (∑' n, h n), (Real.exp_pos _).le⟩

theorem translationScale_ne_zero (h : RealSequences) : translationScale h ≠ 0 := by
  intro hc
  have he := congrArg (fun c : ℝ≥0 => (c : ℝ)) hc
  exact (Real.exp_pos (∑' n, h n)).ne' he

def translatedCorner (h : RealSequences) : Set RealSequences :=
  (fun x : RealSequences => x + h) ⁻¹' stageSet 0

theorem translatedCorner_measurable (h : RealSequences) : MeasurableSet (translatedCorner h) :=
  (measurable_id.add_const h) (measurable_stageSet 0)

theorem translatedCorner_mass (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    restrictedProductMeasure (translatedCorner h) = (translationScale h : ℝ≥0∞) := by
  have hm := congrArg (fun M : Measure RealSequences => M (stageSet 0))
    (map_summable_restrictedProductMeasure h hs)
  change (restrictedProductMeasure.map (fun x : RealSequences => x + h)) (stageSet 0) =
    (ENNReal.ofReal (Real.exp (∑' n, h n)) • restrictedProductMeasure) (stageSet 0) at hm
  rw [Measure.map_apply (by fun_prop : Measurable (fun x : RealSequences => x + h))
    (measurable_stageSet 0), Measure.smul_apply, restrictedProductMeasure_base,
    smul_eq_mul, mul_one] at hm
  exact hm.trans (ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le)

theorem translatedCorner_finite (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    restrictedProductMeasure (translatedCorner h) ≠ ∞ := by
  rw [translatedCorner_mass h hs]
  exact ENNReal.coe_ne_top

theorem translatedCorner_mass_eq_base_iff (h : RealSequences)
    (hs : Summable (fun n => |h n|)) :
    restrictedProductMeasure (translatedCorner h) = restrictedProductMeasure (stageSet 0) ↔
      (∑' n, h n) = 0 := by
  rw [translatedCorner_mass h hs, restrictedProductMeasure_base]
  constructor
  · intro hc
    have he := congrArg ENNReal.toReal hc
    have hexp : Real.exp (∑' n, h n) = 1 := by
      simpa only [ENNReal.coe_toReal, ENNReal.toReal_one, translationScale, NNReal.coe_mk] using he
    exact Real.exp_injective (hexp.trans Real.exp_zero.symm)
  · intro hzero
    have hc : translationScale h = 1 := by
      apply Subtype.ext
      change Real.exp (∑' n, h n) = 1
      simp [hzero]
    rw [hc, ENNReal.coe_one]

def translatedCornerEquiv (h : RealSequences) :
    (RealSequences × RationalGroup) ≃ᵐ (RealSequences × RationalGroup) :=
  (MeasurableEquiv.addRight h).prodCongr (MeasurableEquiv.refl RationalGroup)

theorem translatedCorner_preserving (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    MeasurePreserving (translatedCornerEquiv h)
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h))
      (translationScale h • cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  let e := MeasurableEquiv.addRight h
  have he : MeasurePreserving e restrictedProductMeasure (translationScale h • restrictedProductMeasure) := by
    refine ⟨e.measurable, ?_⟩
    change restrictedProductMeasure.map (fun x => x + h) =
      (translationScale h : ℝ≥0∞) • restrictedProductMeasure
    rw [map_summable_restrictedProductMeasure h hs,
      ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
    rfl
  have heA := he.restrict_preimage_emb e.measurableEmbedding (stageSet 0)
  have hF := heA.prod (MeasurePreserving.id (Measure.count : Measure RationalGroup))
  change MeasurePreserving (translatedCornerEquiv h)
    ((restrictedProductMeasure.restrict (translatedCorner h)).prod Measure.count)
    (((translationScale h : ℝ≥0∞) • restrictedProductMeasure).restrict (stageSet 0) |>.prod Measure.count) at hF
  rw [Measure.restrict_smul, Measure.prod_smul_left] at hF
  exact hF

theorem translatedCorner_quasiMeasurePreserving (h : RealSequences)
    (hs : Summable (fun n => |h n|)) :
    Measure.QuasiMeasurePreserving (translatedCornerEquiv h)
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h))
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  refine ⟨(translatedCornerEquiv h).measurable, ?_⟩
  rw [(translatedCorner_preserving h hs).map_eq]
  exact Measure.smul_absolutelyContinuous

def translatedCornerPullback (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    Lp ℂ 2 (translationScale h • cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)) :=
  pullbackUnitary _ _ (translatedCornerEquiv h) (translatedCornerEquiv h).symm
    (translatedCorner_preserving h hs) ((translatedCorner_preserving h hs).symm (translatedCornerEquiv h))
    (Eventually.of_forall (fun p => (translatedCornerEquiv h).symm_apply_apply p))

theorem translatedCornerPullback_coe (h : RealSequences) (hs : Summable (fun n => |h n|))
    (f : Lp ℂ 2 (translationScale h • cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))) :
    translatedCornerPullback h hs f =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
      fun p => f (translatedCornerEquiv h p) :=
  Lp.coeFn_compMeasurePreserving f (translatedCorner_preserving h hs)

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.translatedCornerPullback
