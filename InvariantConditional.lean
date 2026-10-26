import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace MeasureEquivalenceErgodicDecomposition

/-- A separate type for the same points equipped with the invariant
sigma-algebra. It keeps the two measurable-space structures explicit. -/
def InvariantBase (_G Z : Type*) := Z

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]

/-- The ambient measurable sets that are exactly invariant under the
whole group form a sigma-algebra. -/
@[reducible] def invariantSigma : MeasurableSpace Z where
  MeasurableSet' s := MeasurableSet s ∧ ∀ g : G, (fun z => g • z) ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ => rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, fun g => by
    rw [preimage_compl, hs.2 g]⟩
  measurableSet_iUnion s hs := ⟨MeasurableSet.iUnion (fun n => (hs n).1), fun g => by
    simp_rw [preimage_iUnion, fun n => (hs n).2 g]⟩

theorem invariantSigma_le : invariantSigma (G := G) (Z := Z) ≤ ‹MeasurableSpace Z› :=
  fun _ h => h.1

theorem measurableSet_invariantSigma_iff (s : Set Z) :
    MeasurableSet[invariantSigma (G := G)] s ↔
      MeasurableSet s ∧ ∀ g : G, (fun z => g • z) ⁻¹' s = s := Iff.rfl

instance invariantBaseMeasurableSpace : MeasurableSpace (InvariantBase G Z) :=
  invariantSigma (G := G) (Z := Z)

/-- The identity on points, with the invariant sigma-algebra as target. -/
def invariantBaseMap (z : Z) : InvariantBase G Z := z

theorem invariantBaseMap_measurable : Measurable (invariantBaseMap (G := G) (Z := Z)) :=
  measurable_id'' (invariantSigma_le (G := G))

/-- Every map measurable for the invariant sigma-algebra into a space
with measurable singletons is pointwise invariant. -/
theorem measurable_invariantSigma_eq_smul
    {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : Z → Y) (hf : Measurable[invariantSigma (G := G)] f) :
    ∀ (g : G) (z : Z), f (g • z) = f z := by
  intro g z
  have hset := hf (measurableSet_singleton (f z))
  have hzin : z ∈ f ⁻¹' {f z} := by simp
  have hzpre : z ∈ (fun x : Z => g • x) ⁻¹' (f ⁻¹' {f z}) := by
    rw [hset.2 g]
    exact hzin
  exact hzpre

section Conditional

variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

/-- The actual regular conditional probability kernel of the identity
given the exact invariant sigma-algebra, viewed on the ambient space. -/
noncomputable def invariantConditionalKernel : Kernel Z Z :=
  Kernel.comap (condExpKernel μ (invariantSigma (G := G))) id
    (measurable_id'' (invariantSigma_le (G := G)))

instance invariantConditionalKernel_markov :
    IsMarkovKernel (invariantConditionalKernel (G := G) μ) := by
  unfold invariantConditionalKernel
  infer_instance

theorem invariantConditionalKernel_apply (z : Z) :
    invariantConditionalKernel (G := G) μ z = condExpKernel μ (invariantSigma (G := G)) z := rfl

/-- The conditional measure is constant along each orbit, as an actual
equality of Borel measures, not only on one fixed test set. -/
theorem invariantConditionalKernel_smul (g : G) (z : Z) :
    invariantConditionalKernel (G := G) μ (g • z) =
      invariantConditionalKernel (G := G) μ z := by
  ext s hs
  exact measurable_invariantSigma_eq_smul
    (fun x => condExpKernel μ (invariantSigma (G := G)) x s)
    (measurable_condExpKernel hs) g z

/-- Integrating the invariant conditional kernel reconstructs the
original finite measure. -/
theorem invariantConditionalKernel_comp :
    invariantConditionalKernel (G := G) μ ∘ₘ μ = μ := by
  ext s hs
  have hcomp := congrArg (fun ρ : Measure Z => ρ s)
    (condExpKernel_comp_trim (μ := μ) (invariantSigma_le (G := G)))
  dsimp only at hcomp
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)] at hcomp ⊢
  change (∫⁻ z, condExpKernel μ (invariantSigma (G := G)) z s ∂μ) = μ s
  rw [← lintegral_trim (invariantSigma_le (G := G)) (measurable_condExpKernel hs)]
  exact hcomp

/-- The conditional kernel with its smaller measurable source kept
explicit as a distinct type. -/
noncomputable def invariantBaseKernel : Kernel (InvariantBase G Z) Z :=
  condExpKernel (Ω := Z) μ (invariantSigma (G := G))

instance invariantBaseKernel_markov : IsMarkovKernel (invariantBaseKernel (G := G) μ) := by
  change IsMarkovKernel (condExpKernel (Ω := Z) μ (invariantSigma (G := G)))
  infer_instance

theorem invariantBaseKernel_joint :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ =
      μ.map (fun z => (invariantBaseMap (G := G) z, z)) := by
  have h := compProd_trim_condExpKernel (μ := μ) (invariantSigma_le (G := G))
  rw [trim_eq_map] at h
  exact h

omit [StandardBorelSpace Z] in
/-- Although the invariant base is not pointwise fixed as a type, its
measurable sets are fixed. Consequently the two graph maps below give
identical measures. -/
theorem invariant_graph_action_eq (g : G) (hg : Measurable (fun z : Z => g • z)) :
    μ.map (fun z => (invariantBaseMap (G := G) z, g • z)) =
      μ.map (fun z => (invariantBaseMap (G := G) (g • z), g • z)) := by
  apply Measure.ext_prod
  intro s t hs ht
  have hp1 : Measurable (fun z : Z => (invariantBaseMap (G := G) z, g • z)) :=
    (invariantBaseMap_measurable (G := G)).prodMk hg
  have hp2 : Measurable (fun z : Z => (invariantBaseMap (G := G) (g • z), g • z)) :=
    ((invariantBaseMap_measurable (G := G)).comp hg).prodMk hg
  rw [Measure.map_apply hp1 (hs.prod ht), Measure.map_apply hp2 (hs.prod ht)]
  congr 1
  ext z
  change (z ∈ s ∧ g • z ∈ t) ↔ (g • z ∈ s ∧ g • z ∈ t)
  have hsinv : (fun x : Z => g • x) ⁻¹' s = s := hs.2 g
  have hmem : g • z ∈ s ↔ z ∈ s := by
    change z ∈ (fun x : Z => g • x) ⁻¹' s ↔ z ∈ s
    rw [hsinv]
    rfl
  rw [hmem]

theorem invariantBaseKernel_joint_map (g : G) (hg : Measurable (fun z : Z => g • z)) :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ
        (invariantBaseKernel (G := G) μ).map (fun z => g • z) =
      (μ.map (fun z => g • z)).map (fun z => (invariantBaseMap (G := G) z, z)) := by
  rw [Measure.compProd_map hg, invariantBaseKernel_joint]
  have hp : Measurable (Prod.map (id : InvariantBase G Z → InvariantBase G Z)
      (fun z : Z => g • z)) := measurable_id.prodMap hg
  have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z, z)) :=
    (invariantBaseMap_measurable (G := G)).prodMk measurable_id
  rw [Measure.map_map hp hgraph, Measure.map_map hgraph hg]
  simpa only [Function.comp_def, Prod.map_apply, id_eq] using invariant_graph_action_eq μ g hg

/-- Global nonsingularity descends to almost every actual conditional
measure over the invariant sigma-algebra. -/
theorem invariantConditionalKernel_nonsingular
    [MeasurableSpace.CountablyGenerated Z]
    (g : G) (hg : Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ᵐ z ∂μ,
      (invariantConditionalKernel (G := G) μ z).map (fun w => g • w) ≪
        invariantConditionalKernel (G := G) μ z := by
  have hmap :
      (μ.map (invariantBaseMap (G := G))) ⊗ₘ
          (invariantBaseKernel (G := G) μ).map (fun z => g • z) ≪
        (μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ := by
    rw [invariantBaseKernel_joint_map μ g hg.measurable, invariantBaseKernel_joint]
    exact hg.absolutelyContinuous.map
      ((invariantBaseMap_measurable (G := G)).prodMk measurable_id)
  have hAE := Measure.absolutelyContinuous_compProd_right_iff.mp hmap
  have h := ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable hAE
  simpa only [Kernel.map_apply _ hg.measurable, invariantBaseKernel, invariantConditionalKernel,
    Kernel.comap_apply, invariantBaseMap, id_eq] using h

/-- Countability gives one conull set on which every group element is
nonsingular for the same conditional probability. -/
theorem invariantConditionalKernel_nonsingular_all [Countable G]
    [MeasurableSpace.CountablyGenerated Z]
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ᵐ z ∂μ, ∀ g : G,
      Measure.QuasiMeasurePreserving (fun w : Z => g • w)
        (invariantConditionalKernel (G := G) μ z) (invariantConditionalKernel (G := G) μ z) := by
  have hall := ae_all_iff.mpr (fun g => invariantConditionalKernel_nonsingular μ g (hns g))
  filter_upwards [hall] with z hz
  intro g
  exact ⟨(hns g).measurable, hz g⟩

/-- Each individual invariant measurable set has conditional mass zero
or one, with the expected conditional value. This assertion quantifies
over sets outside the almost-everywhere quantifier. -/
theorem invariantConditionalKernel_real_invariant_set
    (s : Set Z) (hs : MeasurableSet[invariantSigma (G := G)] s) :
    (fun z => (invariantConditionalKernel (G := G) μ z).real s) =ᵐ[μ]
      s.indicator (fun _ => (1 : ℝ)) := by
  have h := condExpKernel_ae_eq_condExp (μ := μ)
    (invariantSigma_le (G := G)) hs.1
  have hsm : StronglyMeasurable[invariantSigma (G := G)]
      (s.indicator (fun _ : Z => (1 : ℝ))) := stronglyMeasurable_const.indicator hs
  have hsi : Integrable (s.indicator (fun _ : Z => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hs.1
  rw [condExp_of_stronglyMeasurable (invariantSigma_le (G := G)) hsm hsi] at h
  exact h

end Conditional

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_smul
#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_comp
#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_nonsingular_all
#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_real_invariant_set
