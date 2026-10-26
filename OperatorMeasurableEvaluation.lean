import OperatorStrongExponential
import OperatorAdjointMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! Borel vector evaluations of the exponential-pair operator coding. -/

open Filter Topology MeasureTheory ContinuousLinearMap

namespace OperatorCoding

section General

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace X]

theorem measurable_operator_action {A : X → H →L[ℂ] H}
    (hA : ∀ v : H, Measurable (fun a => A a v)) {x : X → H} (hx : Measurable x) :
    Measurable (fun a => A a (x a)) := by
  have huncurry := measurable_uncurry_of_continuous_of_measurable
    (u := fun v : H => fun a : X => A a v) (fun a => (A a).continuous) hA
  exact huncurry.comp (hx.prodMk measurable_id)

theorem measurable_operator_pow_apply {A : X → H →L[ℂ] H}
    (hA : ∀ v : H, Measurable (fun a => A a v)) (n : ℕ) (v : H) :
    Measurable (fun a => ((A a) ^ n) v) := by
  induction n with
  | zero => simpa using (measurable_const (a := v) : Measurable (fun _ : X => v))
  | succ n ih =>
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using measurable_operator_action hA ih

theorem measurable_operator_exp_apply {A : X → H →L[ℂ] H}
    (hA : ∀ v : H, Measurable (fun a => A a v)) (v : H) :
    Measurable (fun a => NormedSpace.exp (A a) v) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n a => ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • (((A a) ^ k) v))
  · intro n
    exact (Finset.range n).measurable_sum (fun k _ =>
      (measurable_operator_pow_apply hA k v).const_smul ((k.factorial : ℂ)⁻¹))
  · apply tendsto_pi_nhds.mpr
    intro a
    exact ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (A a)).mapL
      (ContinuousLinearMap.apply ℂ H v)).tendsto_sum_nat

end General

theorem operatorStrong_apply_measurable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : @Measurable (H →L[ℂ] H) H (operatorStrongBorel H) (borel H) (fun T => T x) := by
  letI : TopologicalSpace (H →L[ℂ] H) := operatorStrongTopologyOn H
  letI : MeasurableSpace (H →L[ℂ] H) := operatorStrongBorel H
  letI : BorelSpace (H →L[ℂ] H) := ⟨rfl⟩
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  have he : Continuous (fun T : H →L[ℂ] H => T x) :=
    (continuous_apply x).comp continuous_induced_dom
  exact he.measurable

theorem normalizedRealPart_apply_measurable (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => (normalizedRealPart T : CanonicalOperator) x) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  have hN := (operatorStrong_apply_measurable x).comp normalizeOperator_measurable
  have hD := (canonical_adjoint_apply_measurable x).comp normalizeOperator_measurable
  simpa only [normalizedRealPart, realPart_apply_coe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.star_eq_adjoint] using
    (hN.add hD).const_smul ((2 : ℝ)⁻¹)

theorem normalizedImaginaryPart_apply_measurable (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => (normalizedImaginaryPart T : CanonicalOperator) x) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  have hN := (operatorStrong_apply_measurable x).comp normalizeOperator_measurable
  have hD := (canonical_adjoint_apply_measurable x).comp normalizeOperator_measurable
  simpa only [normalizedImaginaryPart, imaginaryPart_apply_coe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.star_eq_adjoint] using
    ((hN.sub hD).const_smul ((2 : ℝ)⁻¹)).const_smul (-Complex.I)

theorem operatorUnitaryPair_apply_measurable (i : Bool) (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => operatorUnitaryPair T i x) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  cases i
  · have hA : ∀ v : CanonicalHilbert, Measurable (fun T : CanonicalOperator =>
        (Complex.I • (normalizedRealPart T : CanonicalOperator)) v) := by
      intro v
      exact (normalizedRealPart_apply_measurable v).const_smul Complex.I
    simpa only [operatorUnitaryPair, Unitary.coe_linearIsometryEquiv_apply,
      selfAdjoint.expUnitary_coe] using measurable_operator_exp_apply hA x
  · have hA : ∀ v : CanonicalHilbert, Measurable (fun T : CanonicalOperator =>
        (Complex.I • (normalizedImaginaryPart T : CanonicalOperator)) v) := by
      intro v
      exact (normalizedImaginaryPart_apply_measurable v).const_smul Complex.I
    simpa only [operatorUnitaryPair, Unitary.coe_linearIsometryEquiv_apply,
      selfAdjoint.expUnitary_coe] using measurable_operator_exp_apply hA x

end OperatorCoding

#print axioms OperatorCoding.operatorUnitaryPair_apply_measurable
