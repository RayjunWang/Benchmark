import HellingerAffinity
import NonsingularDichotomy

/-! The actual Hellinger zero test on nonsingular ergodic components. -/

open MeasureTheory MeasureTheory.Measure

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceHellinger

variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]

/-- On ergodic nonsingular probability components, zero Hellinger
affinity means failure of measure equivalence. -/
theorem affinity_eq_zero_iff_not_equivalent_of_nonsingular_ergodic
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) μ μ)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (hνerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → ν s = 0 ∨ ν sᶜ = 0) :
    affinity μ ν = 0 ↔ ¬ (μ ≪ ν ∧ ν ≪ μ) := by
  constructor
  · intro hzero heq
    exact (ne_of_gt (affinity_pos_of_absolutelyContinuous μ ν heq.1)) hzero
  · intro hneq
    rcases equivalent_or_mutuallySingular_of_nonsingular_ergodic
      μ ν hμns hνns hμerg hνerg with heq | hsing
    · exact False.elim (hneq heq)
    · exact (affinity_eq_zero_iff_mutuallySingular μ ν).mpr hsing

end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.affinity_eq_zero_iff_not_equivalent_of_nonsingular_ergodic
