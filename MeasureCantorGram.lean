import MeasureCantorDenseFamily

/-! Measurable Gram matrices for the explicit varying-measure L² family.
The parameter measurable structure is the genuine Giry structure on
probability measures, and all entries are actual L² inner products. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

theorem cantorFundamentalVector_inner (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k l : CantorFundamentalIndex) :
    inner ℂ (cantorFundamentalVector μ k) (cantorFundamentalVector μ l) =
      μ.real (cantorCylinder k.1 ∩ cantorCylinder l.1) •
        inner ℂ (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)
          (lp.single 2 l.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert) :=
  L2.inner_indicatorConstLp_indicatorConstLp (cantorCylinder_measurable k.1)
    (cantorCylinder_measurable l.1) (measure_ne_top μ _) (measure_ne_top μ _) _ _

theorem measurable_cantorFundamentalVector_inner (k l : CantorFundamentalIndex) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (cantorFundamentalVector (μ : Measure CantorSpace) l)) := by
  simp only [cantorFundamentalVector_inner, measureReal_def]
  exact (((Measure.measurable_coe ((cantorCylinder_measurable k.1).inter
    (cantorCylinder_measurable l.1))).comp measurable_subtype_coe).ennreal_toReal).smul measurable_const

theorem measurable_cantorFundamentalSequence_inner (i j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalSequence (μ : Measure CantorSpace) i)
        (cantorFundamentalSequence (μ : Measure CantorSpace) j)) :=
  measurable_cantorFundamentalVector_inner (cantorFundamentalEnumeration i) (cantorFundamentalEnumeration j)

noncomputable def cantorIntersectionIndex (k l : CantorCylinderIndex) : CantorCylinderIndex :=
  (cantorCylinder_isSetAlgebra.inter_mem ⟨k, rfl⟩ ⟨l, rfl⟩).choose

theorem cantorIntersectionIndex_spec (k l : CantorCylinderIndex) :
    cantorCylinder (cantorIntersectionIndex k l) = cantorCylinder k ∩ cantorCylinder l :=
  (cantorCylinder_isSetAlgebra.inter_mem ⟨k, rfl⟩ ⟨l, rfl⟩).choose_spec

noncomputable def cantorComplementIndex (k : CantorCylinderIndex) : CantorCylinderIndex :=
  (cantorCylinder_isSetAlgebra.compl_mem ⟨k, rfl⟩).choose

theorem cantorComplementIndex_spec (k : CantorCylinderIndex) :
    cantorCylinder (cantorComplementIndex k) = (cantorCylinder k)ᶜ :=
  (cantorCylinder_isSetAlgebra.compl_mem ⟨k, rfl⟩).choose_spec

theorem vectorCantorMultiplier_fundamental (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (r : CantorCylinderIndex) (k : CantorFundamentalIndex) :
    vectorCantorMultiplier μ r (cantorFundamentalVector μ k) =
      cantorFundamentalVector μ (cantorIntersectionIndex r k.1, k.2) -
        cantorFundamentalVector μ (cantorIntersectionIndex (cantorComplementIndex r) k.1, k.2) := by
  change phaseMap μ (cantorCylinderPhase r) (cantorCylinderPhase_measurable r)
    (cantorCylinderPhase_norm r) (cantorFundamentalVector μ k) = _
  apply Lp.ext
  filter_upwards [phaseMap_coe μ (cantorCylinderPhase r) (cantorCylinderPhase_measurable r)
      (cantorCylinderPhase_norm r) (cantorFundamentalVector μ k),
    indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable k.1)
      (hμs := measure_ne_top μ _) (c := (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)),
    indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable (cantorIntersectionIndex r k.1))
      (hμs := measure_ne_top μ _) (c := (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)),
    indicatorConstLp_coeFn (p := 2)
      (hs := cantorCylinder_measurable (cantorIntersectionIndex (cantorComplementIndex r) k.1))
      (hμs := measure_ne_top μ _) (c := (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)),
    Lp.coeFn_sub (cantorFundamentalVector μ (cantorIntersectionIndex r k.1, k.2))
      (cantorFundamentalVector μ (cantorIntersectionIndex (cantorComplementIndex r) k.1, k.2))]
    with x hphase hk hpos hneg hsub
  simp only [Pi.sub_apply] at hsub
  simp only [cantorFundamentalVector] at hphase hsub ⊢
  rw [hphase, hsub, hpos, hneg, hk]
  rw [cantorIntersectionIndex_spec, cantorIntersectionIndex_spec, cantorComplementIndex_spec]
  classical
  by_cases hr : x ∈ cantorCylinder r <;> by_cases hk : x ∈ cantorCylinder k.1 <;>
    simp [cantorCylinderPhase, hr, hk]

theorem measurable_cantorMultiplierFundamental_inner (r : CantorCylinderIndex)
    (k l : CantorFundamentalIndex) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (vectorCantorMultiplier (μ : Measure CantorSpace) r
          (cantorFundamentalVector (μ : Measure CantorSpace) k))
        (cantorFundamentalVector (μ : Measure CantorSpace) l)) := by
  simp only [vectorCantorMultiplier_fundamental, inner_sub_left]
  exact (measurable_cantorFundamentalVector_inner (cantorIntersectionIndex r k.1, k.2) l).sub
    (measurable_cantorFundamentalVector_inner
      (cantorIntersectionIndex (cantorComplementIndex r) k.1, k.2) l)

end MeasureUnitary

#print axioms MeasureUnitary.measurable_cantorMultiplierFundamental_inner
