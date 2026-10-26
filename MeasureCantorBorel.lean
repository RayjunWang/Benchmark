import MeasureCantorGram
import MeasureVariableGramSchmidt
import OperatorUnitaryBorel

/-! The genuine fixed-Hilbert Borel realization of the amplified
Cantor-cylinder multiplication representations. -/

open MeasureTheory Set Filter InnerProductSpace OperatorCoding
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

local instance : MeasurableSpace CanonicalHilbert := borel _
local instance : BorelSpace CanonicalHilbert := ⟨rfl⟩

abbrev CantorFiber (μ : ProbabilityMeasure CantorSpace) := Lp CanonicalHilbert 2 (μ : Measure CantorSpace)

theorem cantorFundamental_finiteBorelSection (k : CantorFundamentalIndex) :
    FiniteBorelSection (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
      (fun μ => cantorFundamentalVector (μ : Measure CantorSpace) k) := by
  obtain ⟨n, hn⟩ := cantorFundamentalEnumeration_surjective k
  simpa only [cantorFundamentalSequence, Function.comp_apply, hn] using
    finiteBorelSection_raw (fun μ : ProbabilityMeasure CantorSpace =>
      cantorFundamentalSequence (μ : Measure CantorSpace)) n

theorem cantorMultiplier_finiteBorelSection (r : CantorCylinderIndex) (n : ℕ) :
    FiniteBorelSection (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
      (fun μ => vectorCantorMultiplier (μ : Measure CantorSpace) r
        (cantorFundamentalSequence (μ : Measure CantorSpace) n)) := by
  simp only [cantorFundamentalSequence, Function.comp_apply, vectorCantorMultiplier_fundamental]
  exact (cantorFundamental_finiteBorelSection
    (cantorIntersectionIndex r (cantorFundamentalEnumeration n).1, (cantorFundamentalEnumeration n).2)).sub
    (cantorFundamental_finiteBorelSection
      (cantorIntersectionIndex (cantorComplementIndex r) (cantorFundamentalEnumeration n).1,
        (cantorFundamentalEnumeration n).2))

theorem cantorFiberBasis_apply (μ : ProbabilityMeasure CantorSpace) (n : ℕ) :
    cantorFiberBasis (μ : Measure CantorSpace) n = variableSelectedGramSchmidt
      (fun ν : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (ν : Measure CantorSpace)) μ n := by
  unfold cantorFiberBasis
  rw [HilbertBasis.coe_mk]
  rfl

theorem measurable_cantorFiberBasis_multiplier_inner (r : CantorCylinderIndex) (i j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (vectorCantorMultiplier (μ : Measure CantorSpace) r (cantorFiberBasis (μ : Measure CantorSpace) j))) := by
  simp only [cantorFiberBasis_apply]
  exact variableSelectedGramSchmidt_operator_inner_measurable
    (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
    measurable_cantorFundamentalSequence_inner
    (fun μ => cantorFundamentalSequence_nonzero_infinite (μ : Measure CantorSpace))
    (fun μ => (vectorCantorMultiplier (μ : Measure CantorSpace) r).toLinearEquiv.toLinearMap)
    (cantorMultiplier_finiteBorelSection r) i j

noncomputable def cantorCodedUnitary (μ : ProbabilityMeasure CantorSpace) (r : CantorCylinderIndex) :
    StrongUnitary CanonicalHilbert :=
  (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
    ((vectorCantorMultiplier (μ : Measure CantorSpace) r).trans
      (cantorFiberCoordinates (μ : Measure CantorSpace)))

theorem cantorCodedUnitary_coefficient (μ : ProbabilityMeasure CantorSpace) (r : CantorCylinderIndex)
    (i j : ℕ) :
    cantorCodedUnitary μ r (lp.single 2 j (1 : ℂ) : CanonicalHilbert) i =
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (vectorCantorMultiplier (μ : Measure CantorSpace) r (cantorFiberBasis (μ : Measure CantorSpace) j)) := by
  change (cantorFiberBasis (μ : Measure CantorSpace)).repr
    (vectorCantorMultiplier (μ : Measure CantorSpace) r
      ((cantorFiberBasis (μ : Measure CantorSpace)).repr.symm (lp.single 2 j (1 : ℂ)))) i = _
  rw [HilbertBasis.repr_symm_single, HilbertBasis.repr_apply_apply]

theorem measurable_cantorCodedUnitary_basis_apply (r : CantorCylinderIndex) (j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      cantorCodedUnitary μ r (lp.single 2 j (1 : ℂ) : CanonicalHilbert)) := by
  apply canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_iff.mpr
  intro i
  simpa only [Function.comp_apply, cantorCodedUnitary_coefficient] using
    measurable_cantorFiberBasis_multiplier_inner r i j

theorem strongUnitary_measurable_evaluations_of_basis {S : Type*} [MeasurableSpace S]
    (U : S → StrongUnitary CanonicalHilbert)
    (hU : ∀ j : ℕ, Measurable (fun s => U s (lp.single 2 j (1 : ℂ) : CanonicalHilbert)))
    (x : CanonicalHilbert) : Measurable (fun s => U s x) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n s => ∑ j ∈ Finset.range n, (x j) • U s (lp.single 2 j (1 : ℂ) : CanonicalHilbert))
  · intro n
    exact (Finset.range n).measurable_sum (fun j hj => (hU j).const_smul (x j))
  · apply tendsto_pi_nhds.mpr
    intro s
    have hsum := ((U s).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x)).tendsto_sum_nat
    convert hsum using 1
    funext n
    apply Finset.sum_congr rfl
    intro j hj
    have he : (lp.single 2 j (x j) : CanonicalHilbert) =
        (x j) • (lp.single 2 j (1 : ℂ) : CanonicalHilbert) := by
      simpa using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 j (x j) (1 : ℂ))
    rw [he, map_smul]
    rfl

theorem cantorCodedUnitary_measurable (r : CantorCylinderIndex) :
    @Measurable (ProbabilityMeasure CantorSpace) (StrongUnitary CanonicalHilbert)
      inferInstance (borel _) (fun μ => cantorCodedUnitary μ r) :=
  strongUnitary_measurable_of_evaluations _
    (strongUnitary_measurable_evaluations_of_basis _ (measurable_cantorCodedUnitary_basis_apply r))

end

end MeasureUnitary

#print axioms MeasureUnitary.cantorCodedUnitary_measurable
