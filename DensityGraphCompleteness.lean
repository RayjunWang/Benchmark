import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Tactic

/-!
# Abstract density-graph completeness

This verifies the inverse-sequence / closed-graph argument with explicit
analytical interface hypotheses. It does not construct square-root RN densities
or verify those analytical interface hypotheses for L2 measures.
-/

open Filter Set
open scoped Topology

namespace MeasureEquivalenceDensityGraph

variable {K V P : Type*} [Group K] [MetricSpace K] [IsTopologicalGroup K]
  [MetricSpace V] [CompleteSpace V] [TopologicalSpace P] [T2Space P]

/-- Closedness of the feature graph. The predicate `A` models one-sided
absolute continuity; `ν` models a density-to-measure map. -/
theorem isClosed_density_graph (H : Subgroup K) (r : H → V)
    (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    IsClosed (Set.range (fun h : H => ((h : K), r h))) := by
  have limit_identity {u : ℕ → H} {g : K} {v : V}
      (hu : Tendsto (fun n => (u n : K)) atTop (𝓝 g))
      (hv : Tendsto (fun n => r (u n)) atTop (𝓝 v)) : μ g = ν v := by
    have hp := hμ.continuousAt.tendsto.comp hu
    have hq := hν.continuousAt.tendsto.comp hv
    exact tendsto_nhds_unique hp (by simpa only [Function.comp_def, hfactor] using hq)
  apply isSeqClosed_iff_isClosed.mp
  intro s p hs hp
  choose u hu using hs
  have hlim : Tendsto (fun n => ((u n : K), r (u n))) atTop (𝓝 p) := by
    simpa only [hu] using hp
  have hK := (continuous_fst.tendsto p).comp hlim
  have hV := (continuous_snd.tendsto p).comp hlim
  have hforward : μ p.1 = ν p.2 := limit_identity hK hV
  have hC : CauchySeq (fun n => r ((u n)⁻¹)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hV.cauchySeq ε hε
    exact ⟨N, fun i hi j hj => by rw [hinv]; exact hN i hi j hj⟩
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hC
  have hKinv : Tendsto (fun n => (((u n)⁻¹ : H) : K)) atTop (𝓝 p.1⁻¹) := by
    simpa only [Subgroup.coe_inv, Function.comp_def] using hK.inv
  have hback : μ p.1⁻¹ = ν w := limit_identity hKinv hw
  have hpH : p.1 ∈ H := (hH p.1).mpr ⟨hforward.symm ▸ hA p.2, hback.symm ▸ hA w⟩
  refine ⟨⟨p.1, hpH⟩, ?_⟩
  apply Prod.ext
  · rfl
  · apply hνinj
    exact (hfactor ⟨p.1, hpH⟩).trans hforward

/-- Completeness uses only completeness of the ambient parameter metric;
compactness is not required by this abstract result. -/
theorem isComplete_density_graph [CompleteSpace K]
    (H : Subgroup K) (r : H → V) (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    IsComplete (Set.range (fun h : H => ((h : K), r h))) :=
  (isClosed_density_graph H r μ ν A hμ hν hνinj hfactor hA hH hinv).isComplete

/-- The graph equipped with the inherited product metric is a complete metric
space. Pullback to `H` is obtained via its bijective graph parametrization. -/
theorem completeSpace_density_graph [CompleteSpace K]
    (H : Subgroup K) (r : H → V) (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    CompleteSpace (Set.range (fun h : H => ((h : K), r h))) :=
  (isComplete_density_graph H r μ ν A hμ hν hνinj hfactor hA hH hinv).completeSpace_coe

end MeasureEquivalenceDensityGraph

namespace MeasureEquivalenceInverseAC

open MeasureTheory

/-- The measure-specific inverse step: one-sided AC of the inverse translate
gives the opposite AC direction after pushing forward by the bijection. -/
theorem inverse_pushforward_ac {Z : Type*} [MeasurableSpace Z]
    (M : Measure Z) (T : Z ≃ᵐ Z) (h : M.map T.symm ≪ M) :
    M ≪ M.map T := by
  have hmap := T.measurableEmbedding.absolutelyContinuous_map h
  simpa only [MeasurableEquiv.map_map_symm] using hmap

/-- Mutual absolute continuity can therefore be tested using forward and
inverse one-sided absolute continuity. -/
theorem mutual_ac_iff_forward_inverse {Z : Type*} [MeasurableSpace Z]
    (M : Measure Z) (T : Z ≃ᵐ Z) :
    (M.map T ≪ M ∧ M ≪ M.map T) ↔
      (M.map T ≪ M ∧ M.map T.symm ≪ M) := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨hf, ?_⟩
    have hmap := T.symm.measurableEmbedding.absolutelyContinuous_map hb
    simpa only [MeasurableEquiv.map_symm_map] using hmap
  · rintro ⟨hf, hi⟩
    exact ⟨hf, inverse_pushforward_ac M T hi⟩

end MeasureEquivalenceInverseAC

#print axioms MeasureEquivalenceDensityGraph.isClosed_density_graph
#print axioms MeasureEquivalenceDensityGraph.isComplete_density_graph
#print axioms MeasureEquivalenceDensityGraph.completeSpace_density_graph
#print axioms MeasureEquivalenceInverseAC.inverse_pushforward_ac
#print axioms MeasureEquivalenceInverseAC.mutual_ac_iff_forward_inverse
