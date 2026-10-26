import KernelAverages
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import InvariantKernelStationarity

/-! The concrete stationary transition for one countable nonsingular
group action, with fixed space exactly its invariant L2 functions. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z]

noncomputable def groupEnumeration (G : Type*) [Group G] [Countable G] : ℕ → G :=
  (exists_surjective_nat G).choose

theorem groupEnumeration_surjective : Function.Surjective (groupEnumeration G) :=
  (exists_surjective_nat G).choose_spec

noncomputable def groupMoves : ℕ → Z ≃ᵐ Z :=
  fun n => (MeasurableEquiv.smul (groupEnumeration G n) : Z ≃ᵐ Z).symm

theorem ac_of_inverse_map_ac (μ : Measure Z) (e : Z ≃ᵐ Z) (h : μ.map e.symm ≪ μ) :
    μ ≪ μ.map e := by
  have h' := h.map e.measurable
  have heq : (μ.map e.symm).map e = μ := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply]
    exact Measure.map_id
  rw [heq] at h'
  exact h'

variable (μ : Measure Z)
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns

theorem groupMoves_ac : ∀ n, μ.map (groupMoves (G := G) (Z := Z) n) ≪ μ := by
  intro n
  simpa only [groupMoves, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply] using
    (hns (groupEnumeration G n)⁻¹).absolutelyContinuous

theorem groupMoves_back_ac : ∀ n, μ ≪ μ.map (groupMoves (G := G) (Z := Z) n) := by
  intro n
  apply ac_of_inverse_map_ac
  simpa only [groupMoves, MeasurableEquiv.symm_symm, MeasurableEquiv.smul_apply] using
    (hns (groupEnumeration G n)).absolutelyContinuous

theorem groupTransition_fixed_iff [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    normalizedMetropolisTransition μ (groupMoves (G := G)) (groupMoves_ac μ hns) f = f ↔
      ∀ g : G, (fun z => f (g • z)) =ᵐ[μ] f := by
  rw [normalizedMetropolisTransition_fixed_iff μ _ (groupMoves_ac μ hns) (groupMoves_back_ac μ hns)]
  constructor
  · intro h g
    obtain ⟨n, hn⟩ := groupEnumeration_surjective (G := G) g
    filter_upwards [h n] with z hz
    simpa only [groupMoves, MeasurableEquiv.symm_symm, MeasurableEquiv.smul_apply, hn] using hz.symm
  · intro h n
    filter_upwards [h (groupEnumeration G n)] with z hz
    simpa only [groupMoves, MeasurableEquiv.symm_symm, MeasurableEquiv.smul_apply] using hz.symm

theorem groupKernel_noLeak [StandardBorelSpace Z] [Nonempty Z] [IsFiniteMeasure μ]
    [MeasurableEq Z] (s : Set Z)
    (hs : ∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂metropolisKernel μ (groupMoves (G := G)) (groupMoves_ac μ hns) z,
      y ∈ s ↔ z ∈ s := by
  apply metropolisKernel_ae_invariant_set
  intro n
  simpa only [groupMoves, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply] using
    hs (groupEnumeration G n)⁻¹

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.groupTransition_fixed_iff
#print axioms MeasureEquivalenceMarkov.groupKernel_noLeak
