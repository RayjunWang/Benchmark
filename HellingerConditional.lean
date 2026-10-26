import HellingerKernel
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Lemmas
import KernelEquivalence

/-! Affinity disintegration over a measurable quotient fixed by a nonsingular
transformation, with the common marginal and all maps constructed explicitly. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Z Y W : Type*} [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableSpace W]

theorem affinity_map_embedding (f : Z → W) (hf : MeasurableEmbedding f)
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    affinity (μ.map f) (ν.map f) = affinity μ ν := by
  rw [affinity_eq_affinityAgainst (μ.map f) (ν.map f) ((μ+ν).map f)
    (hf.absolutelyContinuous_map (Measure.AbsolutelyContinuous.rfl.add_right ν))
    (hf.absolutelyContinuous_map (Measure.AbsolutelyContinuous.rfl.add_right' μ))]
  rw [affinityAgainst, hf.integral_map, affinity_integral]
  apply integral_congr_ae
  filter_upwards [hf.rnDeriv_map μ (μ+ν), hf.rnDeriv_map ν (μ+ν)] with z hμ hν
  rw [hμ, hν]

section Quotient

variable [StandardBorelSpace Z] [StandardBorelSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (M : Measure Z) [IsFiniteMeasure M]
    (q : Z → Y) (hq : Measurable q)

include hq

theorem quotientGraph_measurableEmbedding : MeasurableEmbedding (fun z => (q z,z)) :=
  (hq.prodMk measurable_id).measurableEmbedding (fun _ _ h => congrArg Prod.snd h)

theorem translated_quotient_joint (κ : Kernel Y Z) [IsFiniteKernel κ]
    (hκ : (M.map q) ⊗ₘ κ = M.map (fun z => (q z,z)))
    (e : Z ≃ᵐ Z) (hfixed : (fun z => q (e z)) =ᵐ[M] q) :
    (M.map e).map (fun z => (q z,z)) = (M.map q) ⊗ₘ κ.map e := by
  calc
    (M.map e).map (fun z => (q z,z)) = M.map (fun z => (q (e z), e z)) := by
      simpa only [Function.comp_def, id_eq] using
        (Measure.map_map (μ := M) (hq.prodMk measurable_id) e.measurable)
    _ = M.map (fun z => (q z, e z)) := Measure.map_congr
      (hfixed.mono (fun z hz => Prod.ext hz rfl))
    _ = (M.map (fun z => (q z,z))).map (Prod.map id e) := by
      symm
      simpa only [Function.comp_def, id_eq, Prod.map_apply] using
        (Measure.map_map (μ := M) (measurable_id.prodMap e.measurable) (hq.prodMk measurable_id))
    _ = (M.map q) ⊗ₘ κ.map e := by
      rw [← hκ, Measure.compProd_map e.measurable]

theorem affinity_over_fixed_quotient (κ : Kernel Y Z) [IsFiniteKernel κ]
    (hκ : (M.map q) ⊗ₘ κ = M.map (fun z => (q z,z)))
    (e : Z ≃ᵐ Z) (hfixed : (fun z => q (e z)) =ᵐ[M] q) :
    affinity M (M.map e) = ∫ y, affinity (κ y) ((κ y).map e) ∂(M.map q) := by
  calc
    affinity M (M.map e) =
        affinity (M.map (fun z => (q z,z))) ((M.map e).map (fun z => (q z,z))) :=
      (affinity_map_embedding _ (quotientGraph_measurableEmbedding q hq) M (M.map e)).symm
    _ = affinity ((M.map q) ⊗ₘ κ) ((M.map q) ⊗ₘ κ.map e) := by
      simp only [← hκ, translated_quotient_joint M q hq κ hκ e hfixed]
    _ = ∫ y, affinity (κ y) ((κ.map e) y) ∂(M.map q) := affinity_compProd (M.map q) κ (κ.map e)
    _ = _ := by simp only [Kernel.map_apply _ e.measurable]

/-- Equivalence of the component measures integrates to equivalence of
the whole measures. This direction does not require that the transformation
already fixes the quotient. -/
theorem equivalent_of_component_equivalence (κ : Kernel Y Z) [IsFiniteKernel κ]
    (hκ : (M.map q) ⊗ₘ κ = M.map (fun z => (q z,z)))
    (e : Z ≃ᵐ Z)
    (heq : ∀ᵐ y ∂(M.map q), κ y ≪ (κ y).map e ∧ (κ y).map e ≪ κ y) :
    M ≪ M.map e ∧ M.map e ≪ M := by
  have hj : MeasureEquivalenceResearch.EquivalentMeasures
      ((M.map q) ⊗ₘ κ) ((M.map q) ⊗ₘ κ.map e) := by
    apply (MeasureEquivalenceResearch.equivalent_compProd_iff (M.map q) κ (κ.map e)).mpr
    simpa only [MeasureEquivalenceResearch.EquivalentMeasures,
      Kernel.map_apply _ e.measurable] using heq
  have hfst : (((M.map q) ⊗ₘ κ).map Prod.snd) = M := by
    rw [hκ]
    have h := Measure.map_map (μ := M) measurable_snd (hq.prodMk measurable_id)
    simpa only [Function.comp_def, id_eq, Measure.map_id'] using h
  have hsnd : (((M.map q) ⊗ₘ κ.map e).map Prod.snd) = M.map e := by
    have hp : (M.map q) ⊗ₘ κ.map e =
        ((M.map q) ⊗ₘ κ).map (Prod.map id e) :=
      Measure.compProd_map (μ := M.map q) (κ := κ) e.measurable
    calc
      _ = (((M.map q) ⊗ₘ κ).map (Prod.map id e)).map Prod.snd :=
        congrArg (Measure.map Prod.snd) hp
      _ = ((M.map q) ⊗ₘ κ).map (fun p => e p.2) := by
        simpa only [Function.comp_def, Prod.map_apply, id_eq] using
          (Measure.map_map (μ := (M.map q) ⊗ₘ κ) measurable_snd
            (measurable_id.prodMap e.measurable))
      _ = (((M.map q) ⊗ₘ κ).map Prod.snd).map e := by
        simpa only [Function.comp_def] using
          (Measure.map_map (μ := (M.map q) ⊗ₘ κ) e.measurable measurable_snd).symm
      _ = M.map e := congrArg (Measure.map e) hfst
  simpa only [hfst, hsnd] using
    And.intro (hj.1.map measurable_snd) (hj.2.map measurable_snd)

end Quotient

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.affinity_map_embedding
#print axioms MeasureEquivalenceHellinger.affinity_over_fixed_quotient
#print axioms MeasureEquivalenceHellinger.equivalent_of_component_equivalence
