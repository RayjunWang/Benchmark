import MeasureCantorBorel
import OperatorBireduction

/-! The actual forward Borel reduction from mutual absolute continuity
of Cantor probability measures to unitary equivalence of bounded operators. -/

open MeasureTheory Set OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance : MeasurableSpace CanonicalHilbert := borel _
local instance : BorelSpace CanonicalHilbert := ⟨rfl⟩
local instance : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel _
local instance : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩

def cantorCylinderEnumeration (n : ℕ) : CantorCylinderIndex := (cantorFundamentalEnumeration n).1

theorem cantorCylinderEnumeration_surjective : Function.Surjective cantorCylinderEnumeration := by
  intro k
  obtain ⟨n, hn⟩ := cantorFundamentalEnumeration_surjective (k, 0)
  exact ⟨n, congrArg Prod.fst hn⟩

def cantorCodedTuple (μ : ProbabilityMeasure CantorSpace) (n : ℕ) : StrongUnitary CanonicalHilbert :=
  cantorCodedUnitary μ (cantorCylinderEnumeration n)

theorem cantorCodedTuple_measurable : Measurable cantorCodedTuple :=
  measurable_pi_iff.mpr (fun n => cantorCodedUnitary_measurable (cantorCylinderEnumeration n))

theorem cantorCodedUnitary_apply (μ : ProbabilityMeasure CantorSpace) (r : CantorCylinderIndex)
    (x : CanonicalHilbert) :
    cantorCodedUnitary μ r x = cantorFiberCoordinates (μ : Measure CantorSpace)
      (vectorCantorMultiplier (μ : Measure CantorSpace) r
        ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x)) := rfl

theorem cantorCodedTuple_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    TupleConjugate (cantorCodedTuple μ) (cantorCodedTuple ν) ↔ MeasureEquivalent μ ν := by
  constructor
  · rintro ⟨W, hW⟩
    apply (amplifiedCantorMultiplierEquivalent_iff (μ : Measure CantorSpace) (ν : Measure CantorSpace)).mp
    let U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).trans
        (W.trans (cantorFiberCoordinates (ν : Measure CantorSpace)).symm)
    refine ⟨U, fun r f => ?_⟩
    obtain ⟨n, hn⟩ := cantorCylinderEnumeration_surjective r
    have heq := congrArg (fun V : StrongUnitary CanonicalHilbert =>
      V (W (cantorFiberCoordinates (μ : Measure CantorSpace) f))) (hW n)
    change W (cantorCodedUnitary μ (cantorCylinderEnumeration n)
      (W.symm (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)))) =
        cantorCodedUnitary ν (cantorCylinderEnumeration n)
          (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)) at heq
    rw [hn, W.symm_apply_apply, cantorCodedUnitary_apply, cantorCodedUnitary_apply,
      LinearIsometryEquiv.symm_apply_apply] at heq
    have hh := congrArg (cantorFiberCoordinates (ν : Measure CantorSpace)).symm heq
    simpa only [U, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using hh
  · intro h
    obtain ⟨U, hU⟩ := (amplifiedCantorMultiplierEquivalent_iff
      (μ : Measure CantorSpace) (ν : Measure CantorSpace)).mpr h
    let W : StrongUnitary CanonicalHilbert :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
        (U.trans (cantorFiberCoordinates (ν : Measure CantorSpace)))
    have hW (r : CantorCylinderIndex) (x : CanonicalHilbert) :
        W (cantorCodedUnitary μ r x) = cantorCodedUnitary ν r (W x) := by
      simpa only [W, cantorCodedUnitary_apply, LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.symm_apply_apply] using
        congrArg (cantorFiberCoordinates (ν : Measure CantorSpace))
          (hU r ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x))
    refine ⟨W, fun n => ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    have hh := hW (cantorCylinderEnumeration n) (W.symm x)
    change W (cantorCodedTuple μ n (W.symm x)) = cantorCodedTuple ν n (W (W.symm x)) at hh
    simpa using hh

def measureCodedOperator (μ : ProbabilityMeasure CantorSpace) : CanonicalOperator :=
  canonicalTupleCodedOperator (cantorCodedTuple μ)

theorem measureCodedOperator_measurable :
    @Measurable (ProbabilityMeasure CantorSpace) CanonicalOperator inferInstance operatorBorel
      measureCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  have hb : (inferInstance : MeasurableSpace (ℕ → StrongUnitary CanonicalHilbert)) =
      borel (ℕ → StrongUnitary CanonicalHilbert) := BorelSpace.measurable_eq
  exact canonicalTupleCodedOperator_continuous.borel_measurable.comp (hb ▸ cantorCodedTuple_measurable)

theorem measureCodedOperator_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    OperatorUnitaryEquivalent (measureCodedOperator μ) (measureCodedOperator ν) ↔ MeasureEquivalent μ ν :=
  (canonicalTupleCodedOperator_equivalent_iff _ _).trans (cantorCodedTuple_equivalent_iff μ ν)

theorem measureCodedOperator_norm_le (μ : ProbabilityMeasure CantorSpace) :
    ‖measureCodedOperator μ‖ ≤ 7 / 8 := canonicalTupleCodedOperator_norm_le _

theorem measureEquivalence_borelReduce_boundedOperators :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace)) operatorBorel
      MeasureEquivalent OperatorUnitaryEquivalent :=
  ⟨measureCodedOperator, measureCodedOperator_measurable, fun μ ν =>
    (measureCodedOperator_equivalent_iff μ ν).symm⟩

end

end MeasureUnitary

#print axioms MeasureUnitary.measureEquivalence_borelReduce_boundedOperators
