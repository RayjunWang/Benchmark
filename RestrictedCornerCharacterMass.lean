import InducedCornerMassReflection
import L2SpectralProjectionIntertwining
import RestrictedInducedReflection

/-! Character and group-generator intertwiners of the actual restricted
product induced modules preserve the finite corner mass. -/

open MeasureTheory Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

local instance : MetricSpace CompactSequences := TopologicalSpace.metrizableSpaceMetric _

theorem pullbackCharacter_eq_cornerPhase (A : Set RealSequences)
    (k : CompactSequences) (i : CharacterIndex)
    (f : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)) :
    pullbackMultiplierL2 (cornerMeasure restrictedProductMeasure A)
      (inducedObservable k) (inducedObservable_measurable k) (characterContinuousMap i) f =
      inducedPhaseUnitary restrictedProductMeasure A (ambientPhase k i)
        (ambientPhase_measurable k i) (ambientPhase_norm k i) f := by
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe (cornerMeasure restrictedProductMeasure A)
    (inducedObservable k) (inducedObservable_measurable k) (characterContinuousMap i) f,
    inducedPhaseUnitary_coe restrictedProductMeasure A (ambientPhase k i)
      (ambientPhase_measurable k i) (ambientPhase_norm k i) f] with p hp hq
  exact hp.trans hq.symm

theorem induced_corner_character_mass_eq (k : CompactSequences)
    (A B : Set RealSequences) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : restrictedProductMeasure A ≠ ∞) (hfinB : restrictedProductMeasure B ≠ ∞)
    (U : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure B))
    (hchar : ∀ (i : CharacterIndex)
      (u : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)),
      U (inducedPhaseUnitary restrictedProductMeasure A (ambientPhase k i)
        (ambientPhase_measurable k i) (ambientPhase_norm k i) u) =
      inducedPhaseUnitary restrictedProductMeasure B (ambientPhase k i)
        (ambientPhase_measurable k i) (ambientPhase_norm k i) (U u))
    (hshift : ∀ (g : RationalGroup)
      (u : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)),
      U (inducedShiftUnitary restrictedProductMeasure A g u) =
        inducedShiftUnitary restrictedProductMeasure B g (U u)) :
    restrictedProductMeasure A = restrictedProductMeasure B := by
  have hcont := continuous_intertwines_of_separating_family
    (cornerMeasure restrictedProductMeasure A) (cornerMeasure restrictedProductMeasure B)
    (inducedObservable k) (inducedObservable k)
    (inducedObservable_measurable k) (inducedObservable_measurable k)
    characterContinuousMap characterContinuousMap_separates U
    (fun i u => by simpa only [pullbackCharacter_eq_cornerPhase] using hchar i u)
  have hproj := projections_intertwine_of_continuous_multipliers
    (cornerMeasure restrictedProductMeasure A) (cornerMeasure restrictedProductMeasure B)
    (inducedObservable k) (inducedObservable k)
    (inducedObservable_measurable k) (inducedObservable_measurable k) U hcont
  apply induced_corner_unitary_mass_eq restrictedProductMeasure rational_smul_preserving
    A B hA hB hfinA hfinB U _ hshift
  intro s hs u
  let F : RealSequences → CompactSequences := fun x => k + sequenceEmbedding x
  have hF : MeasurableEmbedding F :=
    (MeasurableEquiv.addLeft k).measurableEmbedding.comp sequenceEmbedding_measurableEmbedding
  have hFs : MeasurableSet (F '' s) := hF.measurableSet_image.mpr hs
  have hpre : inducedObservable k ⁻¹' (F '' s) = orbitPoint ⁻¹' s := by
    change (F ∘ orbitPoint) ⁻¹' (F '' s) = _
    rw [Set.preimage_comp, Set.preimage_image_eq _ hF.injective]
  have h := hproj (F '' s) hFs u
  simpa only [hpre] using h

theorem induced_corner_character_equivalence_iff_mass (k : CompactSequences)
    (A B : Set RealSequences) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : restrictedProductMeasure A ≠ ∞) (hfinB : restrictedProductMeasure B ≠ ∞) :
    (∃ U : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure B),
      (∀ (i : CharacterIndex)
        (u : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)),
        U (inducedPhaseUnitary restrictedProductMeasure A (ambientPhase k i)
          (ambientPhase_measurable k i) (ambientPhase_norm k i) u) =
        inducedPhaseUnitary restrictedProductMeasure B (ambientPhase k i)
          (ambientPhase_measurable k i) (ambientPhase_norm k i) (U u)) ∧
      (∀ (g : RationalGroup)
        (u : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)),
        U (inducedShiftUnitary restrictedProductMeasure A g u) =
          inducedShiftUnitary restrictedProductMeasure B g (U u))) ↔
      restrictedProductMeasure A = restrictedProductMeasure B := by
  constructor
  · rintro ⟨U, hchar, hshift⟩
    exact induced_corner_character_mass_eq k A B hA hB hfinA hfinB U hchar hshift
  · intro hmass
    obtain ⟨U, hphase, hshift⟩ := exists_induced_corner_unitary restrictedProductMeasure
      rational_smul_preserving rational_smul_ergodic B A hB hA hfinB hmass.symm
    exact ⟨U, fun i u => hphase (ambientPhase k i)
      (ambientPhase_measurable k i) (ambientPhase_norm k i) u, hshift⟩

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.induced_corner_character_mass_eq
