import OperatorHilbertFlatten

/-!
The right-hand Borel bireducibility in Theorem 1.4:
all unitary representations of F∞ and all bounded operators on the same
fixed canonical separable infinite-dimensional Hilbert space.
-/

namespace OperatorCoding

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem fixedHilbertConjugation_equivalent_iff (E : H ≃ₗᵢ[ℂ] K) (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent (E.conjStarAlgEquiv T) (E.conjStarAlgEquiv S) ↔
      OperatorUnitaryEquivalent T S := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨(E.trans Q).trans E.symm, fun x => ?_⟩
    apply E.injective
    simpa using hQ (E x)
  · rintro ⟨Q, hQ⟩
    refine ⟨(E.symm.trans Q).trans E, fun x => ?_⟩
    simpa using congrArg E (hQ (E.symm x))

noncomputable def canonicalTupleCodedOperator (u : ℕ → StrongUnitary CanonicalHilbert) :
    CanonicalOperator := canonicalHilbertSumEquiv.conjStarAlgEquiv (tupleCodedOperator u)

theorem canonicalTupleCodedOperator_equivalent_iff (u v : ℕ → StrongUnitary CanonicalHilbert) :
    OperatorUnitaryEquivalent (canonicalTupleCodedOperator u) (canonicalTupleCodedOperator v) ↔
      TupleConjugate u v :=
  (fixedHilbertConjugation_equivalent_iff _ _ _).trans (tupleCodedOperator_equivalent_iff u v)

theorem canonicalTupleCodedOperator_norm_le (u : ℕ → StrongUnitary CanonicalHilbert) :
    ‖canonicalTupleCodedOperator u‖ ≤ 7 / 8 := by
  rw [canonicalTupleCodedOperator, StarAlgEquiv.norm_map]
  exact tupleCodedOperator_norm_le u

theorem canonicalTupleCodedOperator_continuous :
    @Continuous (ℕ → StrongUnitary CanonicalHilbert) CanonicalOperator
      inferInstance operatorStrongTopology canonicalTupleCodedOperator := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  exact canonicalHilbertSumEquiv.continuous.comp
    (tupleCodedOperator_continuous_apply (canonicalHilbertSumEquiv.symm x))

noncomputable def freeRepresentationCodedOperator (ρ : UnitaryRepresentation (FreeGroup ℕ)) :
    CanonicalOperator := canonicalTupleCodedOperator (fun n => ρ (FreeGroup.of n))

theorem freeRepresentationCodedOperator_continuous :
    @Continuous (UnitaryRepresentation (FreeGroup ℕ)) CanonicalOperator
      (unitaryRepresentationTopology (FreeGroup ℕ)) operatorStrongTopology
      freeRepresentationCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact canonicalTupleCodedOperator_continuous.comp continuous_generator_evaluation

theorem freeRepresentationCodedOperator_equivalent_iff
    (ρ σ : UnitaryRepresentation (FreeGroup ℕ)) :
    OperatorUnitaryEquivalent (freeRepresentationCodedOperator ρ) (freeRepresentationCodedOperator σ) ↔
      UnitaryRepresentationEquivalent ρ σ :=
  (canonicalTupleCodedOperator_equivalent_iff _ _).trans (conjugate_iff_generators ρ σ).symm

theorem freeRepresentations_borelReduce_boundedOperators :
    BorelReducesWith (unitaryRepresentationBorel (FreeGroup ℕ)) operatorBorel
      UnitaryRepresentationEquivalent OperatorUnitaryEquivalent := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact ⟨freeRepresentationCodedOperator, freeRepresentationCodedOperator_continuous.borel_measurable,
    fun ρ σ => (freeRepresentationCodedOperator_equivalent_iff ρ σ).symm⟩

/-- The final comparison in the manuscript's Theorem 1.4, with all spaces,
operators, unitary representations, Borel maps and fixed-space transports
constructed and checked. The strict separation from measure equivalence and
the ℤ comparison are separate goals. -/
theorem freeRepresentations_borelBireducible_boundedOperators :
    BorelBireducibleWith (unitaryRepresentationBorel (FreeGroup ℕ)) operatorBorel
      UnitaryRepresentationEquivalent OperatorUnitaryEquivalent :=
  ⟨freeRepresentations_borelReduce_boundedOperators, boundedOperators_borelReduce_freeRepresentations⟩

end OperatorCoding

#print axioms OperatorCoding.freeRepresentations_borelBireducible_boundedOperators
