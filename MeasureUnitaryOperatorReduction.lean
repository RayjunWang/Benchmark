import MeasureCyclicReduction

/-! The same actual reduction already lands among unitary bounded
operators, hence among normal operators. Its Borel structure is the strong
operator Borel structure, and equivalence is ordinary unitary conjugacy. -/

open MeasureTheory OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel _
local instance : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩

theorem unitaryOperator_continuous :
    @Continuous (StrongUnitary CanonicalHilbert) CanonicalOperator inferInstance operatorStrongTopology
      (fun U => (U : CanonicalOperator)) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi strongUnitary_continuous_eval

theorem unitaryOperator_equivalent_iff (U V : StrongUnitary CanonicalHilbert) :
    OperatorUnitaryEquivalent (U : CanonicalOperator) (V : CanonicalOperator) ↔ ElementConjugate U V := by
  rw [operatorUnitaryEquivalent_iff_conjugate]
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, (conjugateUnitary_iff Q U V).mpr hQ⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, (conjugateUnitary_iff Q U V).mp hQ⟩

def measureCodedUnitaryOperator (μ : ProbabilityMeasure CantorSpace) : CanonicalOperator :=
  (measureCodedUnitary μ : CanonicalOperator)

theorem measureCodedUnitaryOperator_mem_unitary (μ : ProbabilityMeasure CantorSpace) :
    measureCodedUnitaryOperator μ ∈ unitary CanonicalOperator :=
  (Unitary.linearIsometryEquiv.symm (measureCodedUnitary μ)).property

theorem measureCodedUnitaryOperator_normal (μ : ProbabilityMeasure CantorSpace) :
    IsStarNormal (measureCodedUnitaryOperator μ) :=
  isStarNormal_of_mem_unitary (measureCodedUnitaryOperator_mem_unitary μ)

theorem measureCodedUnitaryOperator_measurable :
    @Measurable (ProbabilityMeasure CantorSpace) CanonicalOperator inferInstance operatorBorel
      measureCodedUnitaryOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact unitaryOperator_continuous.borel_measurable.comp measureCodedUnitary_measurable

theorem measureCodedUnitaryOperator_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    OperatorUnitaryEquivalent (measureCodedUnitaryOperator μ) (measureCodedUnitaryOperator ν) ↔
      MeasureEquivalent μ ν :=
  (unitaryOperator_equivalent_iff _ _).trans (measureCodedUnitary_equivalent_iff μ ν)

theorem measureEquivalence_borelReduce_unitaryOperators :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace)) operatorBorel
      MeasureEquivalent OperatorUnitaryEquivalent :=
  ⟨measureCodedUnitaryOperator, measureCodedUnitaryOperator_measurable,
    fun μ ν => (measureCodedUnitaryOperator_equivalent_iff μ ν).symm⟩

end

end MeasureUnitary

#print axioms MeasureUnitary.measureEquivalence_borelReduce_unitaryOperators
