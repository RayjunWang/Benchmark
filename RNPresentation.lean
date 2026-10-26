import RNGraph
import InvariantGraphGroup
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory Set
open scoped Topology ENNReal

namespace MeasureEquivalenceRNPresentation

open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph

variable {K Z G : Type*}
    [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [CompleteSpace K] [SecondCountableTopology K]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem rn_graph_embedding_equiv (e : G ≃* quasiInvariantSubgroup (K := K) M)
    (he : Continuous (fun g : G => (e g : K))) :
    Topology.IsEmbedding (fun g : G =>
      ((e g : K), root (orbit M (e g : K) : Measure Z) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have hgraph := presentation_graph_embedding
    (quasiInvariantSubgroup M) (feature M) (feature_mul_left M) (isClosed_graph M) e he
  have hsub : Topology.IsEmbedding (fun p : K × positiveUnitSphere M =>
      (p.1, (p.2 : Lp ℝ 2 M))) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  exact hsub.comp hgraph

/-- A continuous injective homomorphism whose image is exactly the
quasi-invariance subgroup has an embedded actual RN square-root graph.
No continuity or Borel hypothesis on the root feature is assumed. -/
theorem rn_graph_embedding (i : G →* K) (hi : Continuous i)
    (hinj : Function.Injective i)
    (hrange : Set.range i = (quasiInvariantSubgroup (K := K) M : Set K)) :
    Topology.IsEmbedding (fun g : G =>
      (i g, root (orbit M (i g) : Measure Z) M)) := by
  have hmem (g : G) : i g ∈ quasiInvariantSubgroup (K := K) M := by
    change i g ∈ (quasiInvariantSubgroup (K := K) M : Set K)
    rw [← hrange]
    exact Set.mem_range_self g
  let j : G →* quasiInvariantSubgroup (K := K) M := i.codRestrict _ hmem
  have hjinj : Function.Injective j := by
    intro x y hxy
    exact hinj (congrArg Subtype.val hxy)
  have hjsurj : Function.Surjective j := by
    intro h
    have hh : (h : K) ∈ Set.range i := hrange.symm ▸ h.property
    obtain ⟨g, hg⟩ := hh
    exact ⟨g, Subtype.ext hg⟩
  let e : G ≃* quasiInvariantSubgroup (K := K) M := MulEquiv.ofBijective j ⟨hjinj, hjsurj⟩
  have he (g : G) : (e g : K) = i g := rfl
  have hecont : Continuous (fun g : G => (e g : K)) := by simpa only [he] using hi
  simpa only [he] using rn_graph_embedding_equiv M e hecont

omit [IsTopologicalGroup K] [CompleteSpace K] [SecondCountableTopology K]
    [PolishSpace Z] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] in
theorem rn_distance_invariant (i : G →* K)
    (hrange : Set.range i = (quasiInvariantSubgroup (K := K) M : Set K))
    (a h k : G) :
    dist (root (orbit M (i (a * h)) : Measure Z) M)
      (root (orbit M (i (a * k)) : Measure Z) M) =
    dist (root (orbit M (i h) : Measure Z) M)
      (root (orbit M (i k) : Measure Z) M) := by
  have hmem (g : G) : i g ∈ quasiInvariantSubgroup (K := K) M := by
    change i g ∈ (quasiInvariantSubgroup (K := K) M : Set K)
    rw [← hrange]
    exact Set.mem_range_self g
  have hd := feature_mul_left M ⟨i a, hmem a⟩ ⟨i h, hmem h⟩ ⟨i k, hmem k⟩
  change dist (root (orbit M (i a * i h) : Measure Z) M)
    (root (orbit M (i a * i k) : Measure Z) M) =
    dist (root (orbit M (i h) : Measure Z) M)
      (root (orbit M (i k) : Measure Z) M) at hd
  simpa only [map_mul] using hd

end MeasureEquivalenceRNPresentation

#print axioms MeasureEquivalenceRNPresentation.rn_graph_embedding_equiv
#print axioms MeasureEquivalenceRNPresentation.rn_graph_embedding
#print axioms MeasureEquivalenceRNPresentation.rn_distance_invariant
