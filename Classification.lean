import NegativeReduction
import GaussianPositive
import SampleSpaceTransport

/-! The two research questions, with explicit source relations and actual
mutual absolute continuity of probability measures. Sample-space transport
to Cantor space is added in a separate interface. -/

open MeasureTheory Filter
open scoped Topology

namespace MeasureEquivalenceClassification

abbrev RealSequences := ℕ → ℝ

def LpDifference (p : ℝ) (x y : RealSequences) : Prop :=
  Summable (fun n => |x n - y n| ^ p)

def NullDifference (x y : RealSequences) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

def MeasureEquivalent {Y : Type*} [MeasurableSpace Y]
    (μ ν : ProbabilityMeasure Y) : Prop :=
  (μ : Measure Y) ≪ ν ∧ (ν : Measure Y) ≪ μ

def BorelReduces {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y)

theorem lp_iff_le_two (p : ℝ) (hp : 1 ≤ p) :
    BorelReduces (LpDifference p)
      (MeasureEquivalent (Y := RealSequences)) ↔ p ≤ 2 := by
  constructor
  · intro h
    by_contra! hp2
    exact MeasureEquivalenceNegative.lp_summability_not_borel_reducible
      (Y := RealSequences) p hp2 h
  · intro hp2
    obtain ⟨f, _hc, hm, hred⟩ :=
      MeasureEquivalenceGaussian.exists_continuous_gaussian_reduction_one_le p hp hp2
    exact ⟨f, hm, hred⟩

theorem c0_not_reducible_to_measures
    {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] :
    ¬ BorelReduces NullDifference (MeasureEquivalent (Y := Y)) :=
  MeasureEquivalenceNegative.null_difference_not_borel_reducible

theorem lp_iff_le_two_cantor (p : ℝ) (hp : 1 ≤ p) :
    BorelReduces (LpDifference p)
      (MeasureEquivalent (Y := ℕ → Bool)) ↔ p ≤ 2 := by
  exact (MeasureEquivalenceSampleSpace.exists_reduction_iff
    MeasureEquivalenceSampleSpace.realSequenceEquivCantor (LpDifference p)).symm.trans
      (lp_iff_le_two p hp)

theorem c0_not_reducible_cantor :
    ¬ BorelReduces NullDifference (MeasureEquivalent (Y := ℕ → Bool)) := by
  intro h
  apply c0_not_reducible_to_measures (Y := RealSequences)
  exact (MeasureEquivalenceSampleSpace.exists_reduction_iff
    MeasureEquivalenceSampleSpace.realSequenceEquivCantor NullDifference).mpr h

theorem lp_iff_le_two_standardBorel {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] (hY : ¬ Countable Y) (p : ℝ) (hp : 1 ≤ p) :
    BorelReduces (LpDifference p) (MeasureEquivalent (Y := Y)) ↔ p ≤ 2 := by
  exact (MeasureEquivalenceSampleSpace.exists_reduction_iff
    (MeasureEquivalenceSampleSpace.realSequenceEquiv Y hY) (LpDifference p)).symm.trans
      (lp_iff_le_two p hp)

theorem c0_not_reducible_standardBorel {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] (hY : ¬ Countable Y) :
    ¬ BorelReduces NullDifference (MeasureEquivalent (Y := Y)) := by
  intro h
  apply c0_not_reducible_to_measures (Y := RealSequences)
  exact (MeasureEquivalenceSampleSpace.exists_reduction_iff
    (MeasureEquivalenceSampleSpace.realSequenceEquiv Y hY) NullDifference).mpr h

end MeasureEquivalenceClassification

#print axioms MeasureEquivalenceClassification.lp_iff_le_two
#print axioms MeasureEquivalenceClassification.c0_not_reducible_to_measures
#print axioms MeasureEquivalenceClassification.lp_iff_le_two_cantor
#print axioms MeasureEquivalenceClassification.c0_not_reducible_cantor
#print axioms MeasureEquivalenceClassification.lp_iff_le_two_standardBorel
#print axioms MeasureEquivalenceClassification.c0_not_reducible_standardBorel
