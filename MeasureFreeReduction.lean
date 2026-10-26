import MeasureOperatorReduction

/-! The actual measure-equivalence reduction into all representations of
the countably generated free group, with the pointwise strong Borel space. -/

open MeasureTheory OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel _
local instance : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩

def measureCodedFreeRepresentation (μ : ProbabilityMeasure CantorSpace) :
    UnitaryRepresentation (FreeGroup ℕ) := FreeGroup.lift (cantorCodedTuple μ)

theorem measureCodedFreeRepresentation_measurable :
    @Measurable (ProbabilityMeasure CantorSpace) (UnitaryRepresentation (FreeGroup ℕ))
      inferInstance (unitaryRepresentationBorel (FreeGroup ℕ)) measureCodedFreeRepresentation := by
  have hb : (inferInstance : MeasurableSpace (ℕ → StrongUnitary CanonicalHilbert)) =
      borel (ℕ → StrongUnitary CanonicalHilbert) := BorelSpace.measurable_eq
  exact continuous_lift.borel_measurable.comp (hb ▸ cantorCodedTuple_measurable)

theorem measureCodedFreeRepresentation_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    UnitaryRepresentationEquivalent (measureCodedFreeRepresentation μ) (measureCodedFreeRepresentation ν) ↔
      MeasureEquivalent μ ν :=
  (lift_conjugate_iff (cantorCodedTuple μ) (cantorCodedTuple ν)).trans (cantorCodedTuple_equivalent_iff μ ν)

theorem measureEquivalence_borelReduce_freeRepresentations :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace))
      (unitaryRepresentationBorel (FreeGroup ℕ)) MeasureEquivalent UnitaryRepresentationEquivalent :=
  ⟨measureCodedFreeRepresentation, measureCodedFreeRepresentation_measurable,
    fun μ ν => (measureCodedFreeRepresentation_equivalent_iff μ ν).symm⟩

end

end MeasureUnitary

#print axioms MeasureUnitary.measureEquivalence_borelReduce_freeRepresentations
