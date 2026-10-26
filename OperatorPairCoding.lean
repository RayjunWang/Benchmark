import OperatorTupleCoding
import OperatorBorelNormalization
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

/-! Coding an arbitrary bounded operator by two unitaries using normalized
real and imaginary parts and the exponential on the self-adjoint π-ball. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def conjugateSelfAdjoint (Q : StrongUnitary H)
    (a : selfAdjoint (H →L[ℂ] H)) : selfAdjoint (H →L[ℂ] H) :=
  ⟨Q.conjStarAlgEquiv a, a.property.map Q.conjStarAlgEquiv⟩

theorem conjugateSelfAdjoint_norm (Q : StrongUnitary H) (a : selfAdjoint (H →L[ℂ] H)) :
    ‖conjugateSelfAdjoint Q a‖ = ‖a‖ := by
  change ‖Q.conjStarAlgEquiv (a : H →L[ℂ] H)‖ = ‖(a : H →L[ℂ] H)‖
  exact StarAlgEquiv.norm_map Q.conjStarAlgEquiv (a : H →L[ℂ] H)

theorem expUnitary_conjugate (Q : StrongUnitary H) (a : selfAdjoint (H →L[ℂ] H)) :
    Q.conjStarAlgEquiv (selfAdjoint.expUnitary a : H →L[ℂ] H) =
      (selfAdjoint.expUnitary (conjugateSelfAdjoint Q a) : H →L[ℂ] H) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  simp only [selfAdjoint.expUnitary_coe]
  rw [NormedSpace.map_exp Q.conjStarAlgEquiv (StarAlgEquiv.isometry Q.conjStarAlgEquiv).continuous,
    map_smul]
  rfl

theorem expUnitary_injective_pi_ball (a b : selfAdjoint (H →L[ℂ] H))
    (ha : ‖a‖ < Real.pi) (hb : ‖b‖ < Real.pi)
    (h : (selfAdjoint.expUnitary a : H →L[ℂ] H) = (selfAdjoint.expUnitary b : H →L[ℂ] H)) :
    a = b := by
  have hu : selfAdjoint.expUnitary a = selfAdjoint.expUnitary b := Subtype.ext h
  have hh := congrArg Unitary.argSelfAdjoint hu
  simpa only [argSelfAdjoint_expUnitary ha, argSelfAdjoint_expUnitary hb] using hh

theorem expUnitary_conjugate_reflects (Q : StrongUnitary H)
    (a b : selfAdjoint (H →L[ℂ] H)) (ha : ‖a‖ < Real.pi) (hb : ‖b‖ < Real.pi)
    (h : Q.conjStarAlgEquiv (selfAdjoint.expUnitary a : H →L[ℂ] H) =
      (selfAdjoint.expUnitary b : H →L[ℂ] H)) :
    Q.conjStarAlgEquiv (a : H →L[ℂ] H) = (b : H →L[ℂ] H) := by
  rw [expUnitary_conjugate] at h
  exact congrArg (fun c : selfAdjoint (H →L[ℂ] H) => (c : H →L[ℂ] H))
    (expUnitary_injective_pi_ball _ _ (by rw [conjugateSelfAdjoint_norm]; exact ha) hb h)

theorem conjugateUnitary_iff (Q U V : StrongUnitary H) :
    Q * U * Q⁻¹ = V ↔ Q.conjStarAlgEquiv (U : H →L[ℂ] H) = (V : H →L[ℂ] H) := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun W : StrongUnitary H => W x) h
  · intro h
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun T : H →L[ℂ] H => T x) h

noncomputable def normalizedRealPart (T : H →L[ℂ] H) : selfAdjoint (H →L[ℂ] H) :=
  realPart (normalizeOperator T)

noncomputable def normalizedImaginaryPart (T : H →L[ℂ] H) : selfAdjoint (H →L[ℂ] H) :=
  imaginaryPart (normalizeOperator T)

theorem normalizedRealPart_norm_lt_pi (T : H →L[ℂ] H) : ‖normalizedRealPart T‖ < Real.pi := by
  have h := (realPart.norm_le (normalizeOperator T)).trans_lt (norm_normalizeOperator_lt_one T)
  exact h.trans (by have hp := Real.two_le_pi; linarith)

theorem normalizedImaginaryPart_norm_lt_pi (T : H →L[ℂ] H) :
    ‖normalizedImaginaryPart T‖ < Real.pi := by
  have h := (imaginaryPart.norm_le (normalizeOperator T)).trans_lt (norm_normalizeOperator_lt_one T)
  exact h.trans (by have hp := Real.two_le_pi; linarith)

noncomputable def operatorUnitaryPair (T : H →L[ℂ] H) : Bool → StrongUnitary H
  | false => Unitary.linearIsometryEquiv (selfAdjoint.expUnitary (normalizedRealPart T))
  | true => Unitary.linearIsometryEquiv (selfAdjoint.expUnitary (normalizedImaginaryPart T))

theorem normalizeOperator_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (normalizeOperator T) = normalizeOperator (Q.conjStarAlgEquiv T) := by
  simp only [normalizeOperator, map_smul, StarAlgEquiv.norm_map]

theorem realPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (realPart T : H →L[ℂ] H) = (realPart (Q.conjStarAlgEquiv T) : H →L[ℂ] H) := by
  simp only [realPart_apply_coe, ← Complex.coe_smul, map_smul, map_add]
  exact congrArg (fun A : H →L[ℂ] H => ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • (Q.conjStarAlgEquiv T + A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem imaginaryPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (imaginaryPart T : H →L[ℂ] H) =
      (imaginaryPart (Q.conjStarAlgEquiv T) : H →L[ℂ] H) := by
  simp only [imaginaryPart_apply_coe, ← Complex.coe_smul, map_smul, map_sub]
  exact congrArg (fun A : H →L[ℂ] H => -Complex.I • ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • (Q.conjStarAlgEquiv T - A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem operatorUnitaryPair_reflects (T S : H →L[ℂ] H)
    (h : TupleConjugate (operatorUnitaryPair T) (operatorUnitaryPair S)) :
    OperatorUnitaryEquivalent T S := by
  obtain ⟨Q, hQ⟩ := h
  have hr : Q.conjStarAlgEquiv (normalizedRealPart T : H →L[ℂ] H) = normalizedRealPart S := by
    apply expUnitary_conjugate_reflects Q _ _ (normalizedRealPart_norm_lt_pi T)
      (normalizedRealPart_norm_lt_pi S)
    simpa [operatorUnitaryPair] using (conjugateUnitary_iff Q _ _).mp (hQ false)
  have hi : Q.conjStarAlgEquiv (normalizedImaginaryPart T : H →L[ℂ] H) = normalizedImaginaryPart S := by
    apply expUnitary_conjugate_reflects Q _ _ (normalizedImaginaryPart_norm_lt_pi T)
      (normalizedImaginaryPart_norm_lt_pi S)
    simpa [operatorUnitaryPair] using (conjugateUnitary_iff Q _ _).mp (hQ true)
  apply (normalizeOperator_unitaryEquivalent_iff T S).mp
  apply (operatorUnitaryEquivalent_iff_conjugate _ _).mpr
  refine ⟨Q, ?_⟩
  calc
    Q.conjStarAlgEquiv (normalizeOperator T) =
        Q.conjStarAlgEquiv ((normalizedRealPart T : H →L[ℂ] H) +
          Complex.I • (normalizedImaginaryPart T : H →L[ℂ] H)) := by
      rw [normalizedRealPart, normalizedImaginaryPart, realPart_add_I_smul_imaginaryPart]
    _ = (normalizedRealPart S : H →L[ℂ] H) +
        Complex.I • (normalizedImaginaryPart S : H →L[ℂ] H) := by rw [map_add, map_smul, hr, hi]
    _ = normalizeOperator S := realPart_add_I_smul_imaginaryPart _

theorem operatorUnitaryPair_preserves (T S : H →L[ℂ] H) (h : OperatorUnitaryEquivalent T S) :
    TupleConjugate (operatorUnitaryPair T) (operatorUnitaryPair S) := by
  obtain ⟨Q, hQ⟩ := (operatorUnitaryEquivalent_iff_conjugate T S).mp h
  have hn : Q.conjStarAlgEquiv (normalizeOperator T) = normalizeOperator S := by
    rw [normalizeOperator_conjugate, hQ]
  have hr : conjugateSelfAdjoint Q (normalizedRealPart T) = normalizedRealPart S := by
    apply Subtype.ext
    change Q.conjStarAlgEquiv (realPart (normalizeOperator T) : H →L[ℂ] H) = _
    rw [realPart_conjugate, hn]
    rfl
  have hi : conjugateSelfAdjoint Q (normalizedImaginaryPart T) = normalizedImaginaryPart S := by
    apply Subtype.ext
    change Q.conjStarAlgEquiv (imaginaryPart (normalizeOperator T) : H →L[ℂ] H) = _
    rw [imaginaryPart_conjugate, hn]
    rfl
  refine ⟨Q, fun i => ?_⟩
  apply (conjugateUnitary_iff Q _ _).mpr
  cases i
  · simpa [operatorUnitaryPair, expUnitary_conjugate, hr] using expUnitary_conjugate Q (normalizedRealPart T)
  · simpa [operatorUnitaryPair, expUnitary_conjugate, hi] using expUnitary_conjugate Q (normalizedImaginaryPart T)

theorem operatorUnitaryPair_equivalent_iff (T S : H →L[ℂ] H) :
    TupleConjugate (operatorUnitaryPair T) (operatorUnitaryPair S) ↔ OperatorUnitaryEquivalent T S :=
  ⟨operatorUnitaryPair_reflects T S, operatorUnitaryPair_preserves T S⟩

end OperatorCoding

#print axioms OperatorCoding.operatorUnitaryPair_equivalent_iff
