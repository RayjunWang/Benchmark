import MeasureInducedOperatorCode
import RestrictedInducedReflection

/-! Exact recovery and preservation for the actual induced family code. -/

open MeasureTheory OperatorCoding

namespace MeasureUnitary

variable {H K I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem tupleConjugate_iff_intertwiner (u v : I → StrongUnitary H) :
    TupleConjugate u v ↔ ∃ W : StrongUnitary H, ∀ i x, W (u i x) = v i (W x) := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W, fun i x => ?_⟩
    have h := congrArg (fun V : StrongUnitary H => V (W x)) (hW i)
    change W (u i (W.symm (W x))) = v i (W x) at h
    simpa using h
  · rintro ⟨W, hW⟩
    refine ⟨W, fun i => ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    simpa using hW i (W.symm x)

theorem transportedTuple_intertwiner_iff (E : H ≃ₗᵢ[ℂ] K) (u v : I → StrongUnitary H) :
    TupleConjugate (fun i => E.symm.trans ((u i).trans E)) (fun i => E.symm.trans ((v i).trans E)) ↔
      ∃ W : StrongUnitary H, ∀ i x, W (u i x) = v i (W x) := by
  rw [tupleConjugate_iff_intertwiner]
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨E.trans (Q.trans E.symm), fun i x => ?_⟩
    simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using
      congrArg E.symm (hQ i (E x))
  · rintro ⟨W, hW⟩
    refine ⟨E.symm.trans (W.trans E), fun i x => ?_⟩
    simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using
      congrArg E (hW i (E.symm x))

end MeasureUnitary

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceSolenoid

theorem inducedCodedOperator_equivalent_iff (k l : CompactSequences) :
    OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l) ↔
      ∃ W : StrongUnitary InducedHilbert, ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u) :=
  (canonicalTupleCodedOperator_equivalent_iff _ _).trans
    (MeasureUnitary.transportedTuple_intertwiner_iff inducedCanonicalCoordinates (inducedTuple k) (inducedTuple l))

theorem inducedCodedOperator_preserves_zeroSum (k l : CompactSequences)
    (hkl : l - k ∈ zeroSumSubgroup) :
    OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l) :=
  (inducedCodedOperator_equivalent_iff k l).mpr (exists_inducedTuple_intertwiner_of_zeroSum k l hkl)

theorem inducedCodedOperator_measurable :
    @Measurable CompactSequences CanonicalOperator inferInstance operatorBorel inducedCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  have hb : (inferInstance : MeasurableSpace CompactSequences) = borel CompactSequences :=
    BorelSpace.measurable_eq
  exact hb ▸ inducedCodedOperator_continuous.borel_measurable

theorem inducedCodedOperator_difference_summable (k l : CompactSequences)
    (hkl : OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l)) :
    k - l ∈ summableSubgroup := by
  obtain ⟨W, hW⟩ := (inducedCodedOperator_equivalent_iff k l).mp hkl
  exact inducedTuple_intertwiner_difference_summable k l W hW

theorem inducedCodedOperator_inequivalent_of_nonsummable (k l : CompactSequences)
    (hkl : k - l ∉ summableSubgroup) :
    ¬ OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l) :=
  fun h => hkl (inducedCodedOperator_difference_summable k l h)

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.inducedCodedOperator_equivalent_iff
