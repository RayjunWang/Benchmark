import FiberMultiplicityTransport
import MeasureCharacterIntertwining
import L2SpectralProjectionIntertwining
import UnitaryCyclicSpectralModel

/-! Complete same-base spectral multiplicity classification on counting fibers. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberMultiplicity_classification (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (∃ U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B),
      ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
        U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
          indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f)) ↔
      fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  constructor
  · rintro ⟨U,hU⟩
    exact fiberMultiplicity_eq_of_intertwiner μ A B hA hB U hU
  · intro hcard
    exact ⟨fiberMultiplicityUnitary μ A B hA hB hcard,
      fiberMultiplicityUnitary_intertwines_projections μ A B hA hB hcard⟩

theorem fiberMultiplicityUnitary_intertwines_phase (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B)
    (c : X → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)
    (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    fiberMultiplicityUnitary μ A B hA hB hcard
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) f) =
      phaseEquiv (fiberRestrictedMeasure μ B) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberMultiplicityUnitary μ A B hA hB hcard f) := by
  apply Lp.ext
  filter_upwards [fiberMultiplicityUnitary_coe μ A B hA hB hcard
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) f),
    (fiberNthMatch_preserving μ B A hB hA hcard.symm).quasiMeasurePreserving.ae
      (phaseMap_coe (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) f),
    phaseMap_coe (fiberRestrictedMeasure μ B) (fun p => c p.1) (hc.comp measurable_fst)
      (fun p => hnorm p.1) (fiberMultiplicityUnitary μ A B hA hB hcard f),
    fiberMultiplicityUnitary_coe μ A B hA hB hcard f] with p hleft hin hright hf
  change ((phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
    (fun p => hnorm p.1)) f) (fiberNthMatch B A p) = _ at hin
  change ((phaseEquiv (fiberRestrictedMeasure μ B) (fun p => c p.1) (hc.comp measurable_fst)
    (fun p => hnorm p.1)) (fiberMultiplicityUnitary μ A B hA hB hcard f)) p = _ at hright
  rw [hleft, hin, hright, hf]
  rfl

open OperatorCoding

variable (ρ : Measure SpectralCircle) [IsFiniteMeasure ρ]

def fiberCoordinateUnitary (A : ℕ → Set SpectralCircle) :
    Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure ρ A) :=
  phaseEquiv (fiberRestrictedMeasure ρ A) (fun p => circleCoordinate p.1)
    (circleCoordinate.continuous.measurable.comp measurable_fst)
    (fun p => circleCoordinate_norm p.1)

theorem fiberCoordinateUnitary_intertwiner_projections
    (A B : ℕ → Set SpectralCircle)
    (U : Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure ρ B))
    (hU : ∀ f, U (fiberCoordinateUnitary ρ A f) = fiberCoordinateUnitary ρ B (U f)) :
    ∀ (s : Set SpectralCircle) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure ρ A)),
      U (indicatorL2 (fiberRestrictedMeasure ρ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure ρ B) (hs.preimage measurable_fst) (U f) := by
  apply projections_intertwine_of_continuous_multipliers
    (fiberRestrictedMeasure ρ A) (fiberRestrictedMeasure ρ B)
    Prod.fst Prod.fst measurable_fst measurable_fst U
  apply continuous_intertwines_of_separating_phases
    (fiberRestrictedMeasure ρ A) (fiberRestrictedMeasure ρ B)
    Prod.fst Prod.fst measurable_fst measurable_fst
    (fun _ : Unit => circleCoordinate) (fun _ => circleCoordinate_norm)
  · intro x y hxy
    exact ⟨(), fun h => hxy (Subtype.ext h)⟩
  · intro i f
    exact hU f

theorem fiberCoordinateUnitary_classification (A B : ℕ → Set SpectralCircle)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (∃ U : Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure ρ B),
      ∀ f, U (fiberCoordinateUnitary ρ A f) = fiberCoordinateUnitary ρ B (U f)) ↔
      fiberMultiplicity A =ᵐ[ρ] fiberMultiplicity B := by
  constructor
  · rintro ⟨U,hU⟩
    exact fiberMultiplicity_eq_of_intertwiner ρ A B hA hB U
      (fiberCoordinateUnitary_intertwiner_projections ρ A B U hU)
  · intro hcard
    exact ⟨fiberMultiplicityUnitary ρ A B hA hB hcard,
      fiberMultiplicityUnitary_intertwines_phase ρ A B hA hB hcard circleCoordinate
        circleCoordinate.continuous.measurable circleCoordinate_norm⟩

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberCoordinateUnitary_classification

