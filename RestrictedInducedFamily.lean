import RestrictedCompactAction
import InducedCornerUnitary

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition

abbrev RationalGroup := Multiplicative rationalZeroSumGroup

instance : Countable RationalGroup :=
  (show Function.Injective (Multiplicative.toAdd : RationalGroup → rationalZeroSumGroup) from
    fun _ _ h => congrArg Multiplicative.ofAdd h).countable
instance : MeasurableSpace RationalGroup := ⊤
instance : MeasurableSingletonClass RationalGroup := ⟨fun _ => trivial⟩

instance : MulAction RationalGroup RealSequences where
  smul q x := rationalTranslation (Multiplicative.toAdd q) x
  one_smul x := by
    change x + rationalRealShift (0 : ℕ →₀ ℚ) = x
    rw [map_zero, add_zero]
  mul_smul q r x := (rationalTranslation_add _ _ _).symm

instance : MeasurableConstSMul RationalGroup RealSequences :=
  ⟨fun q => measurable_id.add_const _⟩

theorem rational_smul_preserving (q : RationalGroup) :
    MeasurePreserving (fun x : RealSequences => q • x)
      restrictedProductMeasure restrictedProductMeasure :=
  measurePreserving_rationalTranslation (Multiplicative.toAdd q)

theorem rational_smul_ergodic (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : RationalGroup, (fun x : RealSequences => q • x) ⁻¹' E = E) :
    restrictedProductMeasure E = 0 ∨ restrictedProductMeasure Eᶜ = 0 :=
  rationalZeroSum_ergodic E hE (fun q => Filter.EventuallyEq.of_eq (hinv (Multiplicative.ofAdd q)))

def ambientPhase (k : CompactSequences) (i : CharacterIndex) (x : RealSequences) : ℂ :=
  character i (k + sequenceEmbedding x)

theorem ambientPhase_measurable (k : CompactSequences) (i : CharacterIndex) :
    Measurable (ambientPhase k i) :=
  (character_continuous i).measurable.comp
    (measurable_const.add sequenceEmbedding_continuous.measurable)

theorem ambientPhase_norm (k : CompactSequences) (i : CharacterIndex) (x : RealSequences) :
    ‖ambientPhase k i x‖ = 1 := character_norm _ _

abbrev InducedHilbert :=
  Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))

def inducedFamilyPhase (k : CompactSequences) (i : CharacterIndex) :
    InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert :=
  inducedPhaseUnitary restrictedProductMeasure (stageSet 0) (ambientPhase k i)
    (ambientPhase_measurable k i) (ambientPhase_norm k i)

def inducedFamilyShift (q : RationalGroup) : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert :=
  inducedShiftUnitary restrictedProductMeasure (stageSet 0) q

theorem base_corner_measure_eq_base_product :
    cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0) =
      tailProbability.prod (Measure.count : Measure RationalGroup) := by
  rw [cornerMeasure, restrictedProductMeasure_restrict 0, stageMeasure_zero]

theorem exists_induced_H_intertwiner (h : RealSequences)
    (hs : Summable (fun n => |h n|)) (hzero : (∑' n, h n) = 0) (k : CompactSequences) :
    ∃ W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert,
      (∀ i u, W (inducedFamilyPhase k i u) = inducedFamilyPhase (k + sequenceEmbedding h) i (W u)) ∧
      (∀ q u, W (inducedFamilyShift q u) = inducedFamilyShift q (W u)) := by
  let B := stageSet 0
  let A := (fun x : RealSequences => x + h) ⁻¹' B
  have hB : MeasurableSet B := measurable_stageSet 0
  have hA : MeasurableSet A := (measurable_id.add_const h) hB
  let e := MeasurableEquiv.addRight h
  have he : MeasurePreserving e restrictedProductMeasure restrictedProductMeasure := by
    refine ⟨e.measurable, ?_⟩
    change restrictedProductMeasure.map (fun x => x + h) = restrictedProductMeasure
    rw [map_summable_restrictedProductMeasure h hs, hzero, Real.exp_zero,
      ENNReal.ofReal_one, one_smul]
  have hmA : restrictedProductMeasure A = restrictedProductMeasure B := by
    exact he.measure_preimage hB.nullMeasurableSet
  have hfin : restrictedProductMeasure B ≠ ∞ := by
    change restrictedProductMeasure (stageSet 0) ≠ ∞
    rw [restrictedProductMeasure_base]
    exact ENNReal.one_ne_top
  obtain ⟨U, hUphase, hUshift⟩ := exists_induced_corner_unitary restrictedProductMeasure
    rational_smul_preserving rational_smul_ergodic B A hB hA hfin hmA.symm
  let F := e.prodCongr (MeasurableEquiv.refl RationalGroup)
  have hF : MeasurePreserving F
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure B) :=
    (he.restrict_preimage_emb e.measurableEmbedding B).prod (MeasurePreserving.id Measure.count)
  let V := pullbackUnitary
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure B)
    F F.symm hF (hF.symm F) (ae_of_all _ F.symm_apply_apply)
  have hV (u : InducedHilbert) :
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure A]
        (fun p => u (F p)) := Lp.coeFn_compMeasurePreserving u hF
  refine ⟨V.trans U, ?_, ?_⟩
  · intro i u
    change U (V (inducedFamilyPhase k i u)) =
      inducedPhaseUnitary restrictedProductMeasure B (ambientPhase (k + sequenceEmbedding h) i)
        (ambientPhase_measurable _ _) (ambientPhase_norm _ _) (U (V u))
    rw [← hUphase (ambientPhase (k + sequenceEmbedding h) i)
      (ambientPhase_measurable _ _) (ambientPhase_norm _ _) (V u)]
    congr 1
    apply Lp.ext
    filter_upwards [hV (inducedFamilyPhase k i u),
      hF.quasiMeasurePreserving.ae (inducedPhaseUnitary_coe restrictedProductMeasure B
        (ambientPhase k i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u),
      inducedPhaseUnitary_coe restrictedProductMeasure A
        (ambientPhase (k + sequenceEmbedding h) i) (ambientPhase_measurable _ _)
        (ambientPhase_norm _ _) (V u), hV u] with p hleft hinside hright hVp
    rw [hleft]
    change (inducedPhaseUnitary restrictedProductMeasure B (ambientPhase k i)
      (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u) (F p) = _
    rw [hinside, hright, hVp]
    congr 1
    change character i (k + sequenceEmbedding (p.1 + h +
      rationalRealShift (Multiplicative.toAdd p.2 : rationalZeroSumGroup))) =
      character i (k + sequenceEmbedding h + sequenceEmbedding (p.1 +
        rationalRealShift (Multiplicative.toAdd p.2 : rationalZeroSumGroup)))
    simp only [map_add]
    congr 1
    abel
  · intro q u
    change U (V (inducedFamilyShift q u)) =
      inducedShiftUnitary restrictedProductMeasure B q (U (V u))
    rw [← hUshift q (V u)]
    congr 1
    apply Lp.ext
    filter_upwards [hV (inducedFamilyShift q u),
      hF.quasiMeasurePreserving.ae (inducedShiftUnitary_coe restrictedProductMeasure B q u),
      inducedShiftUnitary_coe restrictedProductMeasure A q (V u),
      (indexShift_preserving restrictedProductMeasure A q⁻¹).quasiMeasurePreserving.ae (hV u)]
      with p hleft hinside hright hVp
    rw [hleft]
    change (inducedShiftUnitary restrictedProductMeasure B q u) (F p) = _
    rw [hinside, hright, hVp]
    rfl

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.exists_induced_H_intertwiner
