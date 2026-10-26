import CouplingMixture
import CouplingKernel
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The actual Markov kernel of the Metropolis coupling stays in the
countable move relation and preserves the original measure. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

def moveRelation (e : ℕ → Z ≃ᵐ Z) (x y : Z) : Prop :=
  x = y ∨ ∃ n, y = e n x ∨ y = (e n).symm x

theorem moveRelation_measurable [MeasurableEq Z]
    (e : ℕ → Z ≃ᵐ Z) : MeasurableSet {z : Z × Z | moveRelation e z.1 z.2} := by
  have hset : {z : Z × Z | moveRelation e z.1 z.2} =
      {z : Z × Z | z.1 = z.2} ∪
        ⋃ n : ℕ, ({z : Z × Z | z.2 = e n z.1} ∪ {z : Z × Z | z.2 = (e n).symm z.1}) := by
    ext z
    simp [moveRelation]
  rw [hset]
  apply (measurableSet_eq_fun measurable_fst measurable_snd).union
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_eq_fun measurable_snd ((e n).measurable.comp measurable_fst)).union
    (measurableSet_eq_fun measurable_snd ((e n).symm.measurable.comp measurable_fst))

theorem completedCoupling_ae_relation (μ ν : Measure Z) (e : Z ≃ᵐ Z)
    (R : Z → Z → Prop) (hR : MeasurableSet {z : Z × Z | R z.1 z.2})
    (hdiag : ∀ z, R z z) (hedge : ∀ z, R z (e.symm z))
    (hreverse : ∀ z, R (e.symm z) z) :
    ∀ᵐ z ∂completedCoupling μ ν e, R z.1 z.2 := by
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) := measurable_id.prodMk e.symm.measurable
  have hdmap : Measurable (fun z : Z => (z,z)) := measurable_id.prodMk measurable_id
  have hA : ∀ᵐ z ∂acceptedEdges ν e, R z.1 z.2 :=
    (ae_map_iff hgraph.aemeasurable hR).mpr (Eventually.of_forall hedge)
  have hArev : ∀ᵐ z ∂acceptedEdges ν e, R z.2 z.1 :=
    (ae_map_iff hgraph.aemeasurable (hR.preimage measurable_swap)).mpr
      (Eventually.of_forall hreverse)
  have hAS : ∀ᵐ z ∂(acceptedEdges ν e).map Prod.swap, R z.1 z.2 :=
    (ae_map_iff measurable_swap.aemeasurable hR).mpr hArev
  have hD : ∀ᵐ z ∂((μ+μ) - (ν + ν.map e.symm)).map (fun z => (z,z)), R z.1 z.2 :=
    (ae_map_iff hdmap.aemeasurable hR).mpr (Eventually.of_forall hdiag)
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨hA,hAS⟩,hD⟩

theorem normalizedMetropolisCoupling_ae_moves [MeasurableEq Z]
    (μ : Measure Z) (e : ℕ → Z ≃ᵐ Z) :
    ∀ᵐ z ∂normalizedMetropolisCoupling μ e, moveRelation e z.1 z.2 := by
  apply Measure.ae_smul_measure
  apply (couplingMixture_ae_iff _ _ geometricWeights_ne_zero _).mpr
  intro n
  apply completedCoupling_ae_relation μ _ (e n) (moveRelation e) (moveRelation_measurable e)
  · intro z
    exact Or.inl rfl
  · intro z
    exact Or.inr ⟨n, Or.inr rfl⟩
  · intro z
    exact Or.inr ⟨n, Or.inl ((e n).apply_symm_apply z).symm⟩

theorem finiteMeasure_of_fst (μ : Measure Z) [IsFiniteMeasure μ]
    (J : Measure (Z × Z)) (hfst : J.map Prod.fst = μ) : IsFiniteMeasure J := by
  have hfinite : IsFiniteMeasure (J.map Prod.fst) := by rw [hfst]; infer_instance
  exact (Measure.isFiniteMeasure_map_iff measurable_fst.aemeasurable).mp hfinite

section Kernel

variable [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z)) [IsFiniteMeasure J]
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

include hfst in
omit [IsFiniteMeasure μ] in
theorem coupling_condKernel_joint : μ ⊗ₘ J.condKernel = J := by
  simpa only [Measure.fst, hfst] using Measure.disintegrate J J.condKernel

include hfst hsnd in
theorem coupling_condKernel_stationary : J.condKernel ∘ₘ μ = μ := by
  rw [← Measure.snd_compProd, coupling_condKernel_joint μ J hfst]
  exact hsnd

theorem couplingTransition_ae_eq_condKernel (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f =ᵐ[μ] fun z => ∫ y, f y ∂J.condKernel z :=
  couplingTransition_ae_eq_integral_kernel μ J hfst hsnd J.condKernel
    (coupling_condKernel_joint μ J hfst).symm f

include hfst in
theorem coupling_condKernel_ae_relation (R : Z → Z → Prop)
    (hR : ∀ᵐ z ∂J, R z.1 z.2) : ∀ᵐ z ∂μ, ∀ᵐ y ∂J.condKernel z, R z y := by
  apply Measure.ae_ae_of_ae_compProd (μ := μ) (κ := J.condKernel)
    (p := fun z : Z × Z => R z.1 z.2)
  rwa [coupling_condKernel_joint μ J hfst]

end Kernel

section ConcreteKernel

variable [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (e : ℕ → Z ≃ᵐ Z)
    (hmap : ∀ n, μ.map (e n) ≪ μ)

include hmap in
theorem normalizedMetropolisCoupling_finite : IsFiniteMeasure (normalizedMetropolisCoupling μ e) :=
  finiteMeasure_of_fst μ _ (normalizedMetropolisCoupling_marginals μ e hmap).1

/-- The actual regular conditional transition kernel of the concrete
normalized stationary Metropolis coupling. -/
noncomputable def metropolisKernel : Kernel Z Z :=
  letI := normalizedMetropolisCoupling_finite μ e hmap
  (normalizedMetropolisCoupling μ e).condKernel

instance metropolisKernel_markov : IsMarkovKernel (metropolisKernel μ e hmap) := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  unfold metropolisKernel
  infer_instance

theorem metropolisKernel_stationary : metropolisKernel μ e hmap ∘ₘ μ = μ := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  exact coupling_condKernel_stationary μ _
    (normalizedMetropolisCoupling_marginals μ e hmap).1
    (normalizedMetropolisCoupling_marginals μ e hmap).2

theorem normalizedMetropolisTransition_ae_eq_kernel (f : Lp ℝ 2 μ) :
    normalizedMetropolisTransition μ e hmap f =ᵐ[μ]
      fun z => ∫ y, f y ∂metropolisKernel μ e hmap z := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  exact couplingTransition_ae_eq_condKernel μ _
    (normalizedMetropolisCoupling_marginals μ e hmap).1
    (normalizedMetropolisCoupling_marginals μ e hmap).2 f

theorem metropolisKernel_ae_moves [MeasurableEq Z] :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂metropolisKernel μ e hmap z, moveRelation e z y := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  exact coupling_condKernel_ae_relation μ _ (normalizedMetropolisCoupling_marginals μ e hmap).1
    (moveRelation e) (normalizedMetropolisCoupling_ae_moves μ e)

omit [StandardBorelSpace Z] [Nonempty Z] in
theorem moveRelation_mem_iff (s : Set Z)
    (hs : ∀ n, (e n) ⁻¹' s = s) {z y : Z} (hmove : moveRelation e z y) :
    y ∈ s ↔ z ∈ s := by
  have hmem (n : ℕ) (x : Z) : e n x ∈ s ↔ x ∈ s := by
    change x ∈ (e n) ⁻¹' s ↔ x ∈ s
    rw [hs n]
  rcases hmove with h | ⟨n,h | h⟩
  · rw [h]
  · rw [h]
    exact hmem n z
  · rw [h]
    simpa only [MeasurableEquiv.apply_symm_apply] using (hmem n ((e n).symm z)).symm

theorem metropolisKernel_ae_invariant_set [MeasurableEq Z] (s : Set Z)
    (hs : ∀ n, (e n) ⁻¹' s = s) :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂metropolisKernel μ e hmap z, y ∈ s ↔ z ∈ s := by
  filter_upwards [metropolisKernel_ae_moves μ e hmap] with z hz
  exact hz.mono (fun y hy => moveRelation_mem_iff e s hs hy)

end ConcreteKernel

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.normalizedMetropolisCoupling_ae_moves
#print axioms MeasureEquivalenceMarkov.coupling_condKernel_stationary
#print axioms MeasureEquivalenceMarkov.couplingTransition_ae_eq_condKernel
#print axioms MeasureEquivalenceMarkov.metropolisKernel_stationary
#print axioms MeasureEquivalenceMarkov.metropolisKernel_ae_invariant_set
