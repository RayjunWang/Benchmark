import UnitaryFullSpectralModel
import FiberL2SpectralSum

/-! The genuine fiber model for a countable cyclic spectral decomposition
with a finite dominating measure. The supplied absolute-continuity facts
are precisely the Radon–Nikodym support identities, not a classification
assumption. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]
    (U : StrongUnitary H) (ρ : Measure SpectralCircle) [IsFiniteMeasure ρ]
    (A : ℕ → Set SpectralCircle)
    (hμρ : ∀ n, greedySpectralMeasure U n ≪ ρ.restrict (A n))
    (hρμ : ∀ n, ρ.restrict (A n) ≪ greedySpectralMeasure U n)

def unitaryDominatedSumEquiv :
    lp (fun n => Lp ℂ 2 (ρ.restrict (A n))) 2 ≃ₗᵢ[ℂ] UnitarySpectralSum U :=
  hilbertFamilyCongr (fun n => rnWeightedEquiv (ρ.restrict (A n))
    (greedySpectralMeasure U n) (hρμ n) (hμρ n))

theorem unitaryDominatedSumEquiv_intertwines
    (f : lp (fun n => Lp ℂ 2 (ρ.restrict (A n))) 2) :
    unitaryDominatedSumEquiv U ρ A hμρ hρμ
      (fiberSumPhaseUnitary ρ A circleCoordinate circleCoordinate.continuous.measurable
        circleCoordinate_norm f) =
      spectralSumUnitary U (unitaryDominatedSumEquiv U ρ A hμρ hρμ f) := by
  apply lp.ext
  funext n
  change rnWeightedEquiv (ρ.restrict (A n)) (greedySpectralMeasure U n) (hρμ n) (hμρ n)
      (phaseEquiv (ρ.restrict (A n)) circleCoordinate circleCoordinate.continuous.measurable
        circleCoordinate_norm (f n)) =
    phaseEquiv (greedySpectralMeasure U n) circleCoordinate circleCoordinate.continuous.measurable
      circleCoordinate_norm (rnWeightedEquiv (ρ.restrict (A n))
        (greedySpectralMeasure U n) (hρμ n) (hμρ n) (f n))
  exact rnWeightedEquiv_intertwines_phase (ρ.restrict (A n)) circleCoordinate
    circleCoordinate.continuous.measurable circleCoordinate_norm (greedySpectralMeasure U n)
      (hρμ n) (hμρ n) (f n)

def unitaryDominatedFiberEquiv (hA : ∀ n, MeasurableSet (A n)) :
    Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] H :=
  ((fiberL2SumEquiv ρ A hA).symm.trans (unitaryDominatedSumEquiv U ρ A hμρ hρμ)).trans
    (unitarySpectralSumEquiv U)

theorem unitaryDominatedFiberEquiv_intertwines (hA : ∀ n, MeasurableSet (A n))
    (f : Lp ℂ 2 (fiberRestrictedMeasure ρ A)) :
    unitaryDominatedFiberEquiv U ρ A hμρ hρμ hA (fiberCoordinateUnitary ρ A f) =
      U (unitaryDominatedFiberEquiv U ρ A hμρ hρμ hA f) := by
  have hf : (fiberL2SumEquiv ρ A hA).symm (fiberCoordinateUnitary ρ A f) =
      fiberSumPhaseUnitary ρ A circleCoordinate circleCoordinate.continuous.measurable
        circleCoordinate_norm ((fiberL2SumEquiv ρ A hA).symm f) := by
    apply (fiberL2SumEquiv ρ A hA).injective
    rw [LinearIsometryEquiv.apply_symm_apply, fiberL2SumEquiv_intertwines_phase,
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  change unitarySpectralSumEquiv U (unitaryDominatedSumEquiv U ρ A hμρ hρμ
    ((fiberL2SumEquiv ρ A hA).symm (fiberCoordinateUnitary ρ A f))) = _
  rw [hf, unitaryDominatedSumEquiv_intertwines, unitarySpectralSumEquiv_intertwines]
  rfl

variable (V : StrongUnitary H) (B : ℕ → Set SpectralCircle)
    (hνρ : ∀ n, greedySpectralMeasure V n ≪ ρ.restrict (B n))
    (hρν : ∀ n, ρ.restrict (B n) ≪ greedySpectralMeasure V n)

include hμρ hρμ hνρ hρν in
theorem unitaryDominatedFiber_classification
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n)) :
    (∃ W : H ≃ₗᵢ[ℂ] H, ∀ x, W (U x) = V (W x)) ↔
      fiberMultiplicity A =ᵐ[ρ] fiberMultiplicity B := by
  let FA := unitaryDominatedFiberEquiv U ρ A hμρ hρμ hA
  let FB := unitaryDominatedFiberEquiv V ρ B hνρ hρν hB
  have hFA (f : Lp ℂ 2 (fiberRestrictedMeasure ρ A)) :
      FA (fiberCoordinateUnitary ρ A f) = U (FA f) :=
    unitaryDominatedFiberEquiv_intertwines U ρ A hμρ hρμ hA f
  have hFB (f : Lp ℂ 2 (fiberRestrictedMeasure ρ B)) :
      FB (fiberCoordinateUnitary ρ B f) = V (FB f) :=
    unitaryDominatedFiberEquiv_intertwines V ρ B hνρ hρν hB f
  rw [← fiberCoordinateUnitary_classification ρ A B hA hB]
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨(FA.trans W).trans FB.symm, ?_⟩
    intro f
    apply FB.injective
    change FB (FB.symm (W (FA (fiberCoordinateUnitary ρ A f)))) =
      FB (fiberCoordinateUnitary ρ B (FB.symm (W (FA f))))
    rw [LinearIsometryEquiv.apply_symm_apply, hFA, hW, hFB,
      LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨C,hC⟩
    refine ⟨(FA.symm.trans C).trans FB, ?_⟩
    intro x
    have hi : FA.symm (U x) = fiberCoordinateUnitary ρ A (FA.symm x) := by
      apply FA.injective
      rw [LinearIsometryEquiv.apply_symm_apply, hFA, LinearIsometryEquiv.apply_symm_apply]
    change FB (C (FA.symm (U x))) = V (FB (C (FA.symm x)))
    rw [hi,hC,hFB]

end
end OperatorCoding

#print axioms OperatorCoding.unitaryDominatedFiber_classification

