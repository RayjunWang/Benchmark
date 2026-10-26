import MeasureUnitaryMultipliers
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Countably many genuine L² multiplication unitaries, one for every
clopen finite-coordinate Cantor cylinder. Equivalent measures give
intertwining representations through the actual RN unitary. -/

open MeasureTheory Set

namespace MeasureUnitary

abbrev CantorSpace := ℕ → Bool
abbrev CantorCylinderIndex := Σ s : Finset ℕ, Set (∀ i : s, Bool)

instance : Countable CantorCylinderIndex := inferInstance

def cantorCylinder (k : CantorCylinderIndex) : Set CantorSpace :=
  cylinder k.1 k.2

theorem cantorCylinder_measurable (k : CantorCylinderIndex) : MeasurableSet (cantorCylinder k) := by
  exact (Set.to_countable k.2).measurableSet.cylinder

noncomputable def cantorCylinderPhase (k : CantorCylinderIndex) (x : CantorSpace) : ℂ :=
  by classical exact if x ∈ cantorCylinder k then 1 else -1

theorem cantorCylinderPhase_measurable (k : CantorCylinderIndex) : Measurable (cantorCylinderPhase k) := by
  classical
  exact Measurable.ite (cantorCylinder_measurable k) measurable_const measurable_const

theorem cantorCylinderPhase_norm (k : CantorCylinderIndex) (x : CantorSpace) :
    ‖cantorCylinderPhase k x‖ = 1 := by
  classical
  unfold cantorCylinderPhase
  split_ifs <;> norm_num

noncomputable def cantorMultiplier (μ : Measure CantorSpace) (k : CantorCylinderIndex) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  phaseEquiv μ (cantorCylinderPhase k) (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k)

/-- Unitary equivalence of the actual varying L² representations. A fixed
canonical Hilbert-space Borel realization is an additional construction. -/
def CantorMultiplierEquivalent (μ ν : Measure CantorSpace) : Prop :=
  ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν, ∀ k f, U (cantorMultiplier μ k f) = cantorMultiplier ν k (U f)

theorem equivalentMeasures_cantorMultiplierEquivalent (μ ν : Measure CantorSpace)
    [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    CantorMultiplierEquivalent μ ν := by
  refine ⟨rnWeightedEquiv μ ν hμν hνμ, fun k f => ?_⟩
  exact rnWeightedEquiv_intertwines_phase μ (cantorCylinderPhase k)
    (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) ν hμν hνμ f

theorem cantorCylinder_range : Set.range cantorCylinder = measurableCylinders (fun _ : ℕ => Bool) := by
  ext s
  constructor
  · rintro ⟨⟨I, S⟩, rfl⟩
    exact cylinder_mem_measurableCylinders _ _ (Set.to_countable S).measurableSet
  · intro hs
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
    exact ⟨⟨I, S⟩, rfl⟩

theorem cantorCylinder_generates :
    MeasurableSpace.generateFrom (Set.range cantorCylinder) = (inferInstance : MeasurableSpace CantorSpace) := by
  rw [cantorCylinder_range, generateFrom_measurableCylinders]

theorem cantorCylinder_isPiSystem : IsPiSystem (Set.range cantorCylinder) := by
  rw [cantorCylinder_range]
  exact isPiSystem_measurableCylinders

end MeasureUnitary

#print axioms MeasureUnitary.equivalentMeasures_cantorMultiplierEquivalent
