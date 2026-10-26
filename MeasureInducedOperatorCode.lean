import RestrictedInducedTuple
import MeasureGramSchmidtBorel
import OperatorBireduction
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Canonical fixed-space realization and bounded-operator coding of the
actual restricted-product induced representation family. -/

open MeasureTheory Set Filter Topology TopologicalSpace OperatorCoding InnerProductSpace
open scoped ENNReal

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureEquivalenceInducedCorners

noncomputable section

instance inducedHilbert_secondCountable : SecondCountableTopology InducedHilbert := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SigmaFinite (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
    rw [base_corner_measure_eq_base_product]
    infer_instance
  infer_instance

def rationalNatElement (n : ℕ) : RationalGroup := Multiplicative.ofAdd
  (⟨Finsupp.single 0 (n : ℚ) - Finsupp.single 1 (n : ℚ), by
    change rationalTotal (Finsupp.single 0 (n : ℚ) - Finsupp.single 1 (n : ℚ)) = 0
    rw [map_sub]
    simp [rationalTotal, Finsupp.liftAddHom_apply]⟩ : rationalZeroSumGroup)

theorem rationalNatElement_injective : Function.Injective rationalNatElement := by
  intro m n h
  have hh := congrArg (fun q : RationalGroup =>
    ((Multiplicative.toAdd q : rationalZeroSumGroup) : ℕ →₀ ℚ) 0) h
  change (Finsupp.single 0 (m : ℚ) - Finsupp.single 1 (m : ℚ) : ℕ →₀ ℚ) 0 =
    (Finsupp.single 0 (n : ℚ) - Finsupp.single 1 (n : ℚ) : ℕ →₀ ℚ) 0 at hh
  simp only [Finsupp.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : ℕ) ≠ 1), sub_zero] at hh
  exact_mod_cast hh

def inducedGroupCell (g : RationalGroup) : Set (RealSequences × RationalGroup) := Set.univ ×ˢ {g}

theorem inducedGroupCell_measurable (g : RationalGroup) : MeasurableSet (inducedGroupCell g) :=
  MeasurableSet.univ.prod (measurableSet_singleton g)

theorem inducedGroupCell_measure (g : RationalGroup) :
    cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0) (inducedGroupCell g) = 1 := by
  rw [base_corner_measure_eq_base_product]
  simp [inducedGroupCell, Measure.prod_prod]

def inducedGroupVector (g : RationalGroup) : InducedHilbert :=
  indicatorConstLp 2 (inducedGroupCell_measurable g)
    (by rw [inducedGroupCell_measure]; exact ENNReal.one_ne_top) (1 : ℂ)

theorem inducedGroupVector_orthonormal : Orthonormal ℂ inducedGroupVector := by
  classical
  rw [orthonormal_iff_ite]
  intro g h
  rw [inducedGroupVector, inducedGroupVector,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one (inducedGroupCell_measurable g)
      (inducedGroupCell_measurable h) (by rw [inducedGroupCell_measure]; exact ENNReal.one_ne_top)
      (by rw [inducedGroupCell_measure]; exact ENNReal.one_ne_top)]
  by_cases he : g = h
  · subst h
    simp only [Set.inter_self, if_true, measureReal_def, inducedGroupCell_measure, ENNReal.toReal_one]
    norm_num
  · have hdis : inducedGroupCell g ∩ inducedGroupCell h = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact he (hp.1.2.symm.trans hp.2.2)
    simp [hdis, he]

theorem inducedHilbert_not_finiteDimensional : ¬ FiniteDimensional ℂ InducedHilbert := by
  intro h
  letI := h
  have hi := (inducedGroupVector_orthonormal.comp rationalNatElement rationalNatElement_injective).linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite _ hi

local instance : MeasurableSpace InducedHilbert := borel _
local instance : BorelSpace InducedHilbert := ⟨rfl⟩

theorem inducedDenseSequence_dense_span :
    (Submodule.span ℂ (Set.range (denseSeq InducedHilbert))).topologicalClosure = ⊤ := by
  apply top_unique
  intro x hx
  have hd : Dense (Set.range (denseSeq InducedHilbert)) := denseRange_denseSeq InducedHilbert
  exact closure_mono (Submodule.subset_span) (hd x)

def inducedCanonicalHilbertBasis : HilbertBasis ℕ ℂ InducedHilbert :=
  MeasureUnitary.selectedGramSchmidtBasis (fun _ : Unit => denseSeq InducedHilbert)
    (fun _ => MeasureUnitary.gramSchmidtNormed_nonzero_infinite (denseSeq InducedHilbert)
      inducedDenseSequence_dense_span inducedHilbert_not_finiteDimensional)
    (fun _ => inducedDenseSequence_dense_span) ()

def inducedCanonicalCoordinates : InducedHilbert ≃ₗᵢ[ℂ] CanonicalHilbert := inducedCanonicalHilbertBasis.repr

def canonicalInducedTuple (k : CompactSequences) (n : ℕ) : StrongUnitary CanonicalHilbert :=
  inducedCanonicalCoordinates.symm.trans ((inducedTuple k n).trans inducedCanonicalCoordinates)

theorem canonicalInducedTuple_continuous : Continuous canonicalInducedTuple := by
  apply continuous_pi
  intro n
  apply (strongUnitary_continuous_iff _).mpr
  intro x
  exact inducedCanonicalCoordinates.continuous.comp
    ((strongUnitary_continuous_eval (inducedCanonicalCoordinates.symm x)).comp
      ((continuous_apply n).comp inducedTuple_continuous))

def inducedCodedOperator (k : CompactSequences) : CanonicalOperator :=
  canonicalTupleCodedOperator (canonicalInducedTuple k)

theorem inducedCodedOperator_continuous :
    @Continuous CompactSequences CanonicalOperator inferInstance operatorStrongTopology inducedCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact canonicalTupleCodedOperator_continuous.comp canonicalInducedTuple_continuous

theorem inducedCodedOperator_norm_le (k : CompactSequences) : ‖inducedCodedOperator k‖ ≤ 7 / 8 :=
  canonicalTupleCodedOperator_norm_le _

end

end MeasureEquivalenceRestrictedPhase

#print axioms MeasureEquivalenceRestrictedPhase.inducedCodedOperator_continuous
