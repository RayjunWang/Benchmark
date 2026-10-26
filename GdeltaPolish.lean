import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Constructions

open Set Topology TopologicalSpace

noncomputable section

namespace BenchmarkJump

/-- Countable intersections of open subsets of a Polish space are Polish
with the inherited topology, via the closed diagonal in a product of open
Polish subspaces. -/
theorem polishSpace_countable_open_intersection
    {X ι : Type*} [TopologicalSpace X] [PolishSpace X] [Countable ι]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) : PolishSpace (⋂ i, U i) := by
  letI : ∀ i, PolishSpace (U i) := fun i => (hU i).polishSpace
  let S : Set X := ⋂ i, U i
  let e : S → X × (∀ i, U i) := fun x =>
    (x, fun i => ⟨x, mem_iInter.mp x.property i⟩)
  have hc : Continuous e := continuous_subtype_val.prodMk
    (continuous_pi fun _ => continuous_subtype_val.subtype_mk _)
  have he : IsEmbedding e :=
    IsEmbedding.of_comp hc continuous_fst (show IsEmbedding (Prod.fst ∘ e) from IsEmbedding.subtypeVal)
  have hRange : range e = {p : X × (∀ i, U i) | ∀ i, (p.2 i : X) = p.1} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩ i
      rfl
    · intro hp
      have hx : p.1 ∈ S := by
        apply mem_iInter.mpr
        intro i
        exact hp i ▸ (p.2 i).property
      refine ⟨⟨p.1, hx⟩, ?_⟩
      apply Prod.ext
      · rfl
      · funext i
        apply Subtype.ext
        exact (hp i).symm
  have hClosed : IsClosed (range e) := by
    rw [hRange]
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
      continuous_fst
  exact (show IsClosedEmbedding e from ⟨he, hClosed⟩).polishSpace

theorem polishSpace_of_isGdelta {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {S : Set X} (hS : IsGδ S) : PolishSpace S := by
  obtain ⟨T, hTo, hTc, hEq⟩ := hS
  letI : Countable T := hTc.to_subtype
  have hEq' : S = ⋂ i : T, (i : Set X) := by
    rw [hEq]
    ext x
    simp only [mem_sInter, mem_iInter]
    exact ⟨fun h i => h i i.property, fun h t ht => h ⟨t, ht⟩⟩
  rw [hEq']
  exact polishSpace_countable_open_intersection (fun i : T => (i : Set X))
    (fun i => hTo i i.property)

#print axioms polishSpace_of_isGdelta

end BenchmarkJump
