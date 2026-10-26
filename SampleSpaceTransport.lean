import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

open MeasureTheory

noncomputable section

namespace MeasureEquivalenceSampleSpace

variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]

/-- Push a probability forward along an actual measurable equivalence. -/
def pushProbability (e : X ≃ᵐ Y) (μ : ProbabilityMeasure X) : ProbabilityMeasure Y :=
  ⟨(μ : Measure X).map e, (μ : Measure X).isProbabilityMeasure_map e.measurable.aemeasurable⟩

theorem measurable_pushProbability (e : X ≃ᵐ Y) : Measurable (pushProbability e) :=
  ((Measure.measurable_map e e.measurable).comp measurable_subtype_coe).subtype_mk

@[simp] theorem pushProbability_symm (e : X ≃ᵐ Y) (μ : ProbabilityMeasure X) :
    pushProbability e.symm (pushProbability e μ) = μ := by
  apply Subtype.ext
  exact MeasurableEquiv.map_symm_map e

/-- The canonical evaluation/Giry spaces of probabilities are measurably equivalent. -/
def probabilityEquiv (e : X ≃ᵐ Y) : ProbabilityMeasure X ≃ᵐ ProbabilityMeasure Y where
  toEquiv :=
    { toFun := pushProbability e
      invFun := pushProbability e.symm
      left_inv := pushProbability_symm e
      right_inv := pushProbability_symm e.symm }
  measurable_toFun := measurable_pushProbability e
  measurable_invFun := measurable_pushProbability e.symm

theorem pushProbability_ac_iff (e : X ≃ᵐ Y) (μ ν : ProbabilityMeasure X) :
    (pushProbability e μ : Measure Y) ≪ pushProbability e ν ↔ (μ : Measure X) ≪ ν := by
  constructor
  · intro h
    have h' := e.symm.measurableEmbedding.absolutelyContinuous_map h
    change ((μ : Measure X).map e).map e.symm ≪ ((ν : Measure X).map e).map e.symm at h'
    simpa only [MeasurableEquiv.map_symm_map] using h'
  · exact e.measurableEmbedding.absolutelyContinuous_map

theorem pushProbability_mutual_ac_iff (e : X ≃ᵐ Y) (μ ν : ProbabilityMeasure X) :
    ((pushProbability e μ : Measure Y) ≪ pushProbability e ν ∧
      (pushProbability e ν : Measure Y) ≪ pushProbability e μ) ↔
    ((μ : Measure X) ≪ ν ∧ (ν : Measure X) ≪ μ) := by
  rw [pushProbability_ac_iff, pushProbability_ac_iff]

theorem transfer_reduction (e : X ≃ᵐ Y) (R : A → A → Prop)
    (f : A → ProbabilityMeasure X) (hf : Measurable f)
    (hred : ∀ x y, R x y ↔ ((f x : Measure X) ≪ f y ∧ (f y : Measure X) ≪ f x)) :
    ∃ g : A → ProbabilityMeasure Y, Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure Y) ≪ g y ∧ (g y : Measure Y) ≪ g x) := by
  refine ⟨pushProbability e ∘ f, (measurable_pushProbability e).comp hf, ?_⟩
  intro x y
  exact (hred x y).trans (pushProbability_mutual_ac_iff e (f x) (f y)).symm

theorem exists_reduction_iff (e : X ≃ᵐ Y) (R : A → A → Prop) :
    (∃ f : A → ProbabilityMeasure X, Measurable f ∧
      ∀ x y, R x y ↔ ((f x : Measure X) ≪ f y ∧ (f y : Measure X) ≪ f x)) ↔
    (∃ g : A → ProbabilityMeasure Y, Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure Y) ≪ g y ∧ (g y : Measure Y) ≪ g x)) := by
  constructor
  · rintro ⟨f, hf, hred⟩
    exact transfer_reduction e R f hf hred
  · rintro ⟨f, hf, hred⟩
    exact transfer_reduction e.symm R f hf hred

theorem realSequence_not_countable : ¬ Countable (ℕ → ℝ) := by
  intro h
  let := h
  have hreal : Countable ℝ := Function.Injective.countable
    (f := fun r : ℝ => fun _ : ℕ => r) (by
      intro r s hrs
      exact congrFun hrs 0)
  exact not_countable (α := ℝ) hreal

def realSequenceEquivCantor : (ℕ → ℝ) ≃ᵐ (ℕ → Bool) :=
  PolishSpace.measurableEquivNatBoolOfNotCountable realSequence_not_countable

def realSequenceEquiv (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y]
    (hY : ¬ Countable Y) : (ℕ → ℝ) ≃ᵐ Y :=
  PolishSpace.measurableEquivOfNotCountable realSequence_not_countable hY

theorem transfer_real_sequence_reduction_to_cantor (R : A → A → Prop)
    (f : A → ProbabilityMeasure (ℕ → ℝ)) (hf : Measurable f)
    (hred : ∀ x y, R x y ↔ ((f x : Measure (ℕ → ℝ)) ≪ f y ∧
      (f y : Measure (ℕ → ℝ)) ≪ f x)) :
    ∃ g : A → ProbabilityMeasure (ℕ → Bool), Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure (ℕ → Bool)) ≪ g y ∧
        (g y : Measure (ℕ → Bool)) ≪ g x) :=
  transfer_reduction realSequenceEquivCantor R f hf hred

theorem transfer_real_sequence_reduction [StandardBorelSpace Y] (hY : ¬ Countable Y)
    (R : A → A → Prop) (f : A → ProbabilityMeasure (ℕ → ℝ)) (hf : Measurable f)
    (hred : ∀ x y, R x y ↔ ((f x : Measure (ℕ → ℝ)) ≪ f y ∧
      (f y : Measure (ℕ → ℝ)) ≪ f x)) :
    ∃ g : A → ProbabilityMeasure Y, Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure Y) ≪ g y ∧ (g y : Measure Y) ≪ g x) :=
  transfer_reduction (realSequenceEquiv Y hY) R f hf hred

end MeasureEquivalenceSampleSpace

#print axioms MeasureEquivalenceSampleSpace.measurable_pushProbability
#print axioms MeasureEquivalenceSampleSpace.probabilityEquiv
#print axioms MeasureEquivalenceSampleSpace.pushProbability_ac_iff
#print axioms MeasureEquivalenceSampleSpace.exists_reduction_iff
#print axioms MeasureEquivalenceSampleSpace.transfer_real_sequence_reduction_to_cantor
#print axioms MeasureEquivalenceSampleSpace.transfer_real_sequence_reduction
