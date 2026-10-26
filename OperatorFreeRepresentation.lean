import OperatorUnitaryBorel

/-! The actual Borel reduction from all bounded operators to all unitary
representations of the countably generated free group. -/

namespace OperatorCoding

def padUnitaryPair {G : Type*} [Group G] (p : Bool → G) (n : ℕ) : G :=
  if n = 0 then p false else if n = 1 then p true else 1

theorem padUnitaryPair_conjugate_iff {G : Type*} [Group G] (p q : Bool → G) :
    TupleConjugate (padUnitaryPair p) (padUnitaryPair q) ↔ TupleConjugate p q := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W, fun i => ?_⟩
    cases i
    · simpa [padUnitaryPair] using hW 0
    · simpa [padUnitaryPair] using hW 1
  · rintro ⟨W, hW⟩
    refine ⟨W, fun n => ?_⟩
    by_cases h₀ : n = 0
    · simpa [padUnitaryPair, h₀] using hW false
    by_cases h₁ : n = 1
    · simpa [padUnitaryPair, h₀, h₁] using hW true
    · simp [padUnitaryPair, h₀, h₁]

noncomputable def operatorUnitarySequence (T : CanonicalOperator) : ℕ → StrongUnitary CanonicalHilbert :=
  padUnitaryPair (operatorUnitaryPair T)

theorem operatorUnitarySequence_equivalent_iff (T S : CanonicalOperator) :
    TupleConjugate (operatorUnitarySequence T) (operatorUnitarySequence S) ↔ OperatorUnitaryEquivalent T S :=
  (padUnitaryPair_conjugate_iff _ _).trans (operatorUnitaryPair_equivalent_iff T S)

theorem operatorUnitarySequence_measurable :
    @Measurable CanonicalOperator (ℕ → StrongUnitary CanonicalHilbert)
      (operatorStrongBorel CanonicalHilbert) (borel (ℕ → StrongUnitary CanonicalHilbert))
      operatorUnitarySequence := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel (StrongUnitary CanonicalHilbert)
  letI : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩
  have hb : (inferInstance : MeasurableSpace (ℕ → StrongUnitary CanonicalHilbert)) =
      borel (ℕ → StrongUnitary CanonicalHilbert) := BorelSpace.measurable_eq
  rw [← hb]
  apply measurable_pi_iff.mpr
  intro n
  by_cases h₀ : n = 0
  · simpa [operatorUnitarySequence, padUnitaryPair, h₀] using operatorUnitaryPair_measurable false
  by_cases h₁ : n = 1
  · simpa [operatorUnitarySequence, padUnitaryPair, h₀, h₁] using operatorUnitaryPair_measurable true
  · simp only [operatorUnitarySequence, padUnitaryPair, if_neg h₀, if_neg h₁]
    exact measurable_const

noncomputable def operatorFreeRepresentation (T : CanonicalOperator) :
    UnitaryRepresentation (FreeGroup ℕ) := FreeGroup.lift (operatorUnitarySequence T)

theorem operatorFreeRepresentation_measurable :
    @Measurable CanonicalOperator (UnitaryRepresentation (FreeGroup ℕ))
      (operatorStrongBorel CanonicalHilbert) (unitaryRepresentationBorel (FreeGroup ℕ))
      operatorFreeRepresentation := by
  have hLift := (continuous_lift (G := StrongUnitary CanonicalHilbert) (ι := ℕ)).borel_measurable
  exact hLift.comp operatorUnitarySequence_measurable

theorem operatorFreeRepresentation_equivalent_iff (T S : CanonicalOperator) :
    UnitaryRepresentationEquivalent (operatorFreeRepresentation T) (operatorFreeRepresentation S) ↔
      OperatorUnitaryEquivalent T S :=
  (lift_conjugate_iff _ _).trans (operatorUnitarySequence_equivalent_iff T S)

theorem boundedOperators_borelReduce_freeRepresentations :
    BorelReducesWith operatorBorel (unitaryRepresentationBorel (FreeGroup ℕ))
      OperatorUnitaryEquivalent UnitaryRepresentationEquivalent :=
  ⟨operatorFreeRepresentation, operatorFreeRepresentation_measurable,
    fun T S => (operatorFreeRepresentation_equivalent_iff T S).symm⟩

end OperatorCoding

#print axioms OperatorCoding.boundedOperators_borelReduce_freeRepresentations
