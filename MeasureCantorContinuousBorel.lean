import MeasureCantorBorel
import MeasureContinuousMultipliers
import MeasureVariableOperatorGram
import MeasureCantorCircle
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Every continuous circle-valued Cantor multiplier has an actual Borel
realization on the one canonical Hilbert space, with the same explicit
Gram–Schmidt coordinates as the cylinder multipliers. -/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance : MeasurableSpace CanonicalHilbert := borel _
local instance : BorelSpace CanonicalHilbert := ⟨rfl⟩

def cantorProbabilityKernel : Kernel (ProbabilityMeasure CantorSpace) CantorSpace where
  toFun μ := (μ : Measure CantorSpace)
  measurable' := measurable_subtype_coe

theorem measurable_continuousMultiplierFundamental_inner (c : C(CantorSpace, ℂ))
    (k l : CantorFundamentalIndex) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (continuousMultiplierL2 (μ : Measure CantorSpace) c
          (cantorFundamentalVector (μ : Measure CantorSpace) l))) := by
  let a : CantorSpace → CanonicalHilbert := (cantorCylinder k.1).indicator
    (fun _ => (lp.single 2 k.2 (1 : ℂ) : CanonicalHilbert))
  let b : CantorSpace → CanonicalHilbert := (cantorCylinder l.1).indicator
    (fun _ => (lp.single 2 l.2 (1 : ℂ) : CanonicalHilbert))
  have ha : Measurable a := measurable_const.indicator (cantorCylinder_measurable k.1)
  have hb : Measurable b := measurable_const.indicator (cantorCylinder_measurable l.1)
  have hm : StronglyMeasurable (fun x => inner ℂ (a x) (c x • b x)) :=
    (ha.inner (c.continuous.measurable.smul hb)).stronglyMeasurable
  have heq : (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (continuousMultiplierL2 (μ : Measure CantorSpace) c
          (cantorFundamentalVector (μ : Measure CantorSpace) l))) =
      fun μ : ProbabilityMeasure CantorSpace => ∫ x, inner ℂ (a x) (c x • b x) ∂(μ : Measure CantorSpace) := by
    funext μ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [continuousMultiplierL2_coe (μ : Measure CantorSpace) c
        (cantorFundamentalVector (μ : Measure CantorSpace) l),
      indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable k.1)
        (hμs := measure_ne_top (μ : Measure CantorSpace) _)
        (c := (lp.single 2 k.2 (1 : ℂ) : CanonicalHilbert)),
      indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable l.1)
        (hμs := measure_ne_top (μ : Measure CantorSpace) _)
        (c := (lp.single 2 l.2 (1 : ℂ) : CanonicalHilbert))] with x hm hk hl
    simp only [cantorFundamentalVector] at hm ⊢
    rw [hm, hk, hl]
  rw [heq]
  exact (hm.integral_kernel (κ := cantorProbabilityKernel)).measurable

def cantorContinuousCodedUnitary (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1)
    (μ : ProbabilityMeasure CantorSpace) : StrongUnitary CanonicalHilbert :=
  (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
    ((phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc).trans
      (cantorFiberCoordinates (μ : Measure CantorSpace)))

theorem cantorContinuousCodedUnitary_coefficient (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1)
    (μ : ProbabilityMeasure CantorSpace) (i j : ℕ) :
    cantorContinuousCodedUnitary c hc μ (lp.single 2 j (1 : ℂ) : CanonicalHilbert) i =
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc
          (cantorFiberBasis (μ : Measure CantorSpace) j)) := by
  change (cantorFiberBasis (μ : Measure CantorSpace)).repr
    (phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc
      ((cantorFiberBasis (μ : Measure CantorSpace)).repr.symm (lp.single 2 j (1 : ℂ)))) i = _
  rw [HilbertBasis.repr_symm_single, HilbertBasis.repr_apply_apply]

theorem measurable_cantorContinuousBasis_inner (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1)
    (i j : ℕ) : Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc
          (cantorFiberBasis (μ : Measure CantorSpace) j))) := by
  simp only [cantorFiberBasis_apply, ← continuousMultiplierL2_phase _ c hc]
  exact variableSelectedGramSchmidt_matrix_measurable
    (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
    measurable_cantorFundamentalSequence_inner
    (fun μ => cantorFundamentalSequence_nonzero_infinite (μ : Measure CantorSpace))
    (fun μ => (continuousMultiplierL2 (μ : Measure CantorSpace) c).toLinearMap)
    (fun m n => measurable_continuousMultiplierFundamental_inner c
      (cantorFundamentalEnumeration m) (cantorFundamentalEnumeration n)) i j

theorem cantorContinuousCodedUnitary_measurable (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1) :
    @Measurable (ProbabilityMeasure CantorSpace) (StrongUnitary CanonicalHilbert)
      inferInstance (borel _) (cantorContinuousCodedUnitary c hc) := by
  apply strongUnitary_measurable_of_evaluations
  apply strongUnitary_measurable_evaluations_of_basis
  intro j
  apply canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_iff.mpr
  intro i
  simpa only [Function.comp_apply, cantorContinuousCodedUnitary_coefficient] using
    measurable_cantorContinuousBasis_inner c hc i j

end

end MeasureUnitary

#print axioms MeasureUnitary.cantorContinuousCodedUnitary_measurable
