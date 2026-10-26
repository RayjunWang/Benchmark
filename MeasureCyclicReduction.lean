import MeasureCantorContinuousBorel
import MeasureOperatorReduction
import OperatorCyclicRepresentation
import SeparatingMultiplierIntertwining

/-! The actual forward cyclic-representation reduction: one injective
circle coordinate, infinite amplification, and Borel canonical coordinates.
Reflection uses Stone–Weierstrass and the explicit cylinder-density proof. -/

open MeasureTheory Set OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance : MeasurableSpace CanonicalHilbert := borel _
local instance : BorelSpace CanonicalHilbert := ⟨rfl⟩
local instance : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel _
local instance : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩

theorem cantorCylinderPhase_continuous (k : CantorCylinderIndex) : Continuous (cantorCylinderPhase k) := by
  classical
  let g : (∀ i : k.1, Bool) → ℂ := fun y => if y ∈ k.2 then 1 else -1
  have heq : cantorCylinderPhase k = fun x => g (fun i : k.1 => x i) := by
    funext x
    rfl
  rw [heq]
  have hp : Continuous (fun x : CantorSpace => fun i : k.1 => x (i : ℕ)) :=
    continuous_pi (fun i => continuous_apply (i : ℕ))
  exact (continuous_of_discreteTopology : Continuous g).comp hp

def cantorCylinderContinuousPhase (k : CantorCylinderIndex) : C(CantorSpace, ℂ) :=
  ⟨cantorCylinderPhase k, cantorCylinderPhase_continuous k⟩

theorem circle_intertwiner_implies_cylinder_intertwiner
    (μ ν : ProbabilityMeasure CantorSpace) (U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν)
    (hU : ∀ f, U (phaseEquiv (μ : Measure CantorSpace) cantorCircleContinuousMap
        cantorCirclePhase_continuous.measurable cantorCirclePhase_norm f) =
      phaseEquiv (ν : Measure CantorSpace) cantorCircleContinuousMap
        cantorCirclePhase_continuous.measurable cantorCirclePhase_norm (U f)) :
    ∀ k f, U (vectorCantorMultiplier (μ : Measure CantorSpace) k f) =
      vectorCantorMultiplier (ν : Measure CantorSpace) k (U f) := by
  let φ : C(CantorSpace, ℂ) →⋆ₐ[ℂ] (CantorFiber ν →L[ℂ] CantorFiber ν) :=
    (U.conjStarAlgEquiv : (CantorFiber μ →L[ℂ] CantorFiber μ) →⋆ₐ[ℂ]
      (CantorFiber ν →L[ℂ] CantorFiber ν)).comp
        (continuousMultiplierStarAlgHom (E := CanonicalHilbert) (μ : Measure CantorSpace))
  let ψ : C(CantorSpace, ℂ) →⋆ₐ[ℂ] (CantorFiber ν →L[ℂ] CantorFiber ν) :=
    continuousMultiplierStarAlgHom (ν : Measure CantorSpace)
  have heq : φ = ψ := by
    apply MeasureEquivalenceRestrictedPhase.starAlgHom_eq_of_separating_family
      φ ψ (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
        (continuousMultiplierL2 (μ : Measure CantorSpace)).continuous)
      (continuousMultiplierL2 (ν : Measure CantorSpace)).continuous
      (fun _ : Unit => cantorCircleContinuousMap)
    · intro x y hxy
      exact ⟨(), fun h => hxy (cantorCirclePhase_injective h)⟩
    · intro i
      apply ContinuousLinearMap.ext
      intro f
      change U (continuousMultiplierL2 (μ : Measure CantorSpace) cantorCircleContinuousMap (U.symm f)) =
        continuousMultiplierL2 (ν : Measure CantorSpace) cantorCircleContinuousMap f
      rw [continuousMultiplierL2_phase _ _ cantorCirclePhase_norm,
        continuousMultiplierL2_phase _ _ cantorCirclePhase_norm]
      simpa using hU (U.symm f)
  intro k f
  have h := congrArg (fun F : C(CantorSpace, ℂ) →⋆ₐ[ℂ] (CantorFiber ν →L[ℂ] CantorFiber ν) =>
    F (cantorCylinderContinuousPhase k) (U f)) heq
  change U (continuousMultiplierL2 (μ : Measure CantorSpace) (cantorCylinderContinuousPhase k)
    (U.symm (U f))) = continuousMultiplierL2 (ν : Measure CantorSpace)
      (cantorCylinderContinuousPhase k) (U f) at h
  rw [U.symm_apply_apply, continuousMultiplierL2_phase _ _ (cantorCylinderPhase_norm k),
    continuousMultiplierL2_phase _ _ (cantorCylinderPhase_norm k)] at h
  exact h

def measureCodedUnitary (μ : ProbabilityMeasure CantorSpace) : StrongUnitary CanonicalHilbert :=
  cantorContinuousCodedUnitary cantorCircleContinuousMap cantorCirclePhase_norm μ

theorem measureCodedUnitary_measurable : Measurable measureCodedUnitary :=
  cantorContinuousCodedUnitary_measurable cantorCircleContinuousMap cantorCirclePhase_norm

theorem measureCodedUnitary_apply (μ : ProbabilityMeasure CantorSpace) (x : CanonicalHilbert) :
    measureCodedUnitary μ x = cantorFiberCoordinates (μ : Measure CantorSpace)
      (phaseEquiv (μ : Measure CantorSpace) cantorCircleContinuousMap
        cantorCirclePhase_continuous.measurable cantorCirclePhase_norm
        ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x)) := rfl

theorem measureCodedUnitary_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    ElementConjugate (measureCodedUnitary μ) (measureCodedUnitary ν) ↔ MeasureEquivalent μ ν := by
  constructor
  · rintro ⟨W, hW⟩
    apply (amplifiedCantorMultiplierEquivalent_iff (μ : Measure CantorSpace) (ν : Measure CantorSpace)).mp
    let U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).trans
        (W.trans (cantorFiberCoordinates (ν : Measure CantorSpace)).symm)
    refine ⟨U, circle_intertwiner_implies_cylinder_intertwiner μ ν U (fun f => ?_)⟩
    have heq := congrArg (fun V : StrongUnitary CanonicalHilbert =>
      V (W (cantorFiberCoordinates (μ : Measure CantorSpace) f))) hW
    change W (measureCodedUnitary μ (W.symm (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)))) =
      measureCodedUnitary ν (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)) at heq
    rw [W.symm_apply_apply, measureCodedUnitary_apply, measureCodedUnitary_apply,
      LinearIsometryEquiv.symm_apply_apply] at heq
    have hh := congrArg (cantorFiberCoordinates (ν : Measure CantorSpace)).symm heq
    simpa only [U, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using hh
  · intro h
    let U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν :=
      rnWeightedEquiv (μ : Measure CantorSpace) (ν : Measure CantorSpace) h.1 h.2
    have hU (f : CantorFiber μ) := rnWeightedEquiv_intertwines_phase (μ : Measure CantorSpace)
      cantorCircleContinuousMap cantorCirclePhase_continuous.measurable cantorCirclePhase_norm
      (ν : Measure CantorSpace) h.1 h.2 f
    let W : StrongUnitary CanonicalHilbert :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
        (U.trans (cantorFiberCoordinates (ν : Measure CantorSpace)))
    have hW (x : CanonicalHilbert) : W (measureCodedUnitary μ x) = measureCodedUnitary ν (W x) := by
      simpa only [W, measureCodedUnitary_apply, LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.symm_apply_apply] using congrArg (cantorFiberCoordinates (ν : Measure CantorSpace))
          (hU ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x))
    refine ⟨W, ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    simpa using hW (W.symm x)

theorem measureEquivalence_borelReduce_unitaries :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace))
      (borel (StrongUnitary CanonicalHilbert)) MeasureEquivalent ElementConjugate :=
  ⟨measureCodedUnitary, measureCodedUnitary_measurable,
    fun μ ν => (measureCodedUnitary_equivalent_iff μ ν).symm⟩

def measureCodedCyclicRepresentation (μ : ProbabilityMeasure CantorSpace) :
    UnitaryRepresentation (Multiplicative ℤ) := zpowersHom _ (measureCodedUnitary μ)

theorem measureEquivalence_borelReduce_cyclicRepresentations :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace))
      (unitaryRepresentationBorel (Multiplicative ℤ)) MeasureEquivalent UnitaryRepresentationEquivalent :=
  ⟨measureCodedCyclicRepresentation, continuous_zpowersHom.borel_measurable.comp measureCodedUnitary_measurable,
    fun μ ν => (measureCodedUnitary_equivalent_iff μ ν).symm.trans (cyclic_conjugate_iff _ _).symm⟩

end

end MeasureUnitary

#print axioms MeasureUnitary.measureEquivalence_borelReduce_cyclicRepresentations
