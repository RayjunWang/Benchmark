import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace SpectralDomination

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def normalizeNonzeroMeasure (μ : Measure Y) [IsFiniteMeasure μ] (hμ : μ ≠ 0) : ProbabilityMeasure Y :=
  ⟨(μ univ)⁻¹ • μ, ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (mt Measure.measure_univ_eq_zero.mp hμ) (measure_ne_top μ univ)⟩⟩

theorem normalizeNonzeroMeasure_equivalent (μ : Measure Y) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    μ ≪ (normalizeNonzeroMeasure μ hμ : Measure Y) ∧
      (normalizeNonzeroMeasure μ hμ : Measure Y) ≪ μ := by
  exact ⟨Measure.absolutelyContinuous_smul (by simp [measure_ne_top]), Measure.smul_absolutelyContinuous⟩

def normalizedKernelProbability (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : ∀ x, κ x ≠ 0)
    (x : X) : ProbabilityMeasure Y := normalizeNonzeroMeasure (κ x) (hκ x)

theorem normalizedKernelProbability_measurable (κ : Kernel X Y) [IsFiniteKernel κ]
    (hκ : ∀ x, κ x ≠ 0) : Measurable (normalizedKernelProbability κ hκ) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun x => (κ x univ)⁻¹ * κ x s)
  exact (Kernel.measurable_coe κ MeasurableSet.univ).inv.mul (Kernel.measurable_coe κ hs)

theorem map_ac_iff_of_measurableEmbedding (f : Y → Z) (hf : MeasurableEmbedding f) (μ ν : Measure Y) :
    μ.map f ≪ ν.map f ↔ μ ≪ ν := by
  constructor
  · intro h
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hzero
    have hz : ν.map f (f '' s) = 0 := by rw [hf.map_apply, hf.injective.preimage_image, hzero]
    have hm := h hz
    rwa [hf.map_apply, hf.injective.preimage_image] at hm
  · intro h
    exact h.map hf.measurable

def standardCantorEmbedding (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y] : Y → ℕ → Bool :=
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y).choose

theorem standardCantorEmbedding_measurableEmbedding [StandardBorelSpace Y] :
    MeasurableEmbedding (standardCantorEmbedding Y) := by
  let h := (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y).choose_spec
  exact h.1.measurableEmbedding h.2

def cantorKernelProbability [StandardBorelSpace Y] (κ : Kernel X Y) [IsFiniteKernel κ]
    (hκ : ∀ x, κ x ≠ 0) (x : X) : ProbabilityMeasure (ℕ → Bool) :=
  ⟨((normalizedKernelProbability κ hκ x : ProbabilityMeasure Y) : Measure Y).map (standardCantorEmbedding Y),
    Measure.isProbabilityMeasure_map (standardCantorEmbedding_measurableEmbedding.measurable.aemeasurable)⟩

theorem cantorKernelProbability_measurable [StandardBorelSpace Y]
    (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : ∀ x, κ x ≠ 0) :
    Measurable (cantorKernelProbability κ hκ) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map _ standardCantorEmbedding_measurableEmbedding.measurable).comp
    (measurable_subtype_coe.comp (normalizedKernelProbability_measurable κ hκ))

theorem cantorKernelProbability_classification [StandardBorelSpace Y]
    (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : ∀ x, κ x ≠ 0) (x y : X) :
    ((cantorKernelProbability κ hκ x : Measure (ℕ → Bool)) ≪ cantorKernelProbability κ hκ y ∧
      (cantorKernelProbability κ hκ y : Measure (ℕ → Bool)) ≪ cantorKernelProbability κ hκ x) ↔
      (κ x ≪ κ y ∧ κ y ≪ κ x) := by
  change ((_ : Measure Y).map (standardCantorEmbedding Y) ≪ (_ : Measure Y).map (standardCantorEmbedding Y) ∧
    (_ : Measure Y).map (standardCantorEmbedding Y) ≪ (_ : Measure Y).map (standardCantorEmbedding Y)) ↔ _
  rw [map_ac_iff_of_measurableEmbedding _ standardCantorEmbedding_measurableEmbedding,
    map_ac_iff_of_measurableEmbedding _ standardCantorEmbedding_measurableEmbedding]
  have hx := normalizeNonzeroMeasure_equivalent (κ x) (hκ x)
  have hy := normalizeNonzeroMeasure_equivalent (κ y) (hκ y)
  constructor
  · rintro ⟨hab,hba⟩
    exact ⟨hx.1.trans (hab.trans hy.2),hy.1.trans (hba.trans hx.2)⟩
  · rintro ⟨hab,hba⟩
    exact ⟨hx.2.trans (hab.trans hy.1),hy.2.trans (hba.trans hx.1)⟩

end SpectralDomination

#print axioms SpectralDomination.cantorKernelProbability_classification
