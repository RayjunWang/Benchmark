import Classification
import GaussianCantor
import InfinityEndpoint

/-! The complete statements of Theorems 1.1 and 1.2 of MeasureEquivalence.tex.
The extended exponent is `WithTop ℝ`; its value `⊤` denotes infinity.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace MeasureEquivalencePaper

open MeasureEquivalenceClassification

abbrev Cantor := ℕ → Bool

def ExtendedLpDifference (p : WithTop ℝ) (x y : RealSequences) : Prop :=
  match p with
  | ⊤ => MeasureEquivalenceInfinity.BoundedDifference x y
  | (r : ℝ) => LpDifference r x y

theorem infinity_not_reducible :
    ¬ BorelReduces MeasureEquivalenceInfinity.BoundedDifference
      (MeasureEquivalent (Y := Cantor)) := by
  rintro ⟨g, hg, hred⟩
  have hp : ¬ BorelReduces (LpDifference 3) (MeasureEquivalent (Y := Cantor)) := by
    intro hh
    have hle := (lp_iff_le_two_cantor 3 (by norm_num)).mp hh
    norm_num at hle
  apply hp
  obtain ⟨f, _hc, hf, hiff⟩ := MeasureEquivalenceInfinity.exists_continuous_lp3_bounded_reduction
  exact ⟨g ∘ f, hg.comp hf, fun x y => (hiff x y).trans (hred (f x) (f y))⟩

/-- Theorem 1.1, including the infinite exponent. -/
theorem theorem_1_1 (p : WithTop ℝ) (hp : (1 : WithTop ℝ) ≤ p) :
    BorelReduces (ExtendedLpDifference p) (MeasureEquivalent (Y := Cantor)) ↔
      p ≤ (2 : WithTop ℝ) := by
  cases p with
  | top => simpa [ExtendedLpDifference] using infinity_not_reducible
  | coe p =>
    have hp' : 1 ≤ p := by simpa using hp
    change BorelReduces (LpDifference p) (MeasureEquivalent (Y := Cantor)) ↔
      (p : WithTop ℝ) ≤ ((2 : ℝ) : WithTop ℝ)
    rw [WithTop.coe_le_coe]
    exact lp_iff_le_two_cantor p hp'

def cutCantorHomeomorph : MeasureEquivalenceGaussianCantor.CutCantor ≃ₜ Cantor :=
  MeasureEquivalenceGaussianCantor.cutCantorHomeomorphNat.trans
    (Homeomorph.piCongrRight (fun _ => Homeomorph.ofDiscrete finTwoEquiv))

/-- The continuous positive conclusion in Theorem 1.1, for weak convergence of probabilities. -/
theorem theorem_1_1_continuous (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ f : RealSequences → ProbabilityMeasure Cantor, Continuous f ∧ Measurable f ∧
      ∀ x y, LpDifference p x y ↔ MeasureEquivalent (f x) (f y) := by
  obtain ⟨f, hf, hm, hiff⟩ :=
    MeasureEquivalenceGaussianCantor.exists_continuous_cantor_reduction_one_le p hp hp2
  let e := cutCantorHomeomorph.toMeasurableEquiv
  refine ⟨MeasureEquivalenceSampleSpace.pushProbability e ∘ f, ?_,
    (MeasureEquivalenceSampleSpace.measurable_pushProbability e).comp hm, ?_⟩
  · have hc : Continuous (MeasureEquivalenceSampleSpace.pushProbability e) := by
      exact ProbabilityMeasure.continuous_map cutCantorHomeomorph.continuous
    exact hc.comp hf
  · intro x y
    exact (hiff x y).trans
      (MeasureEquivalenceSampleSpace.pushProbability_mutual_ac_iff e (f x) (f y)).symm

/-- Theorem 1.2. -/
theorem theorem_1_2 :
    ¬ BorelReduces NullDifference (MeasureEquivalent (Y := Cantor)) :=
  c0_not_reducible_cantor

end MeasureEquivalencePaper

#print axioms MeasureEquivalencePaper.theorem_1_1
#print axioms MeasureEquivalencePaper.theorem_1_1_continuous
#print axioms MeasureEquivalencePaper.theorem_1_2
