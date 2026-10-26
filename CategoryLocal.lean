import CategoryTools

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A countable Baire cover of a nonempty open set has one member comeager
on a smaller nonempty open set. -/
theorem baire_cover_local_residual [BaireSpace X] {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, BaireMeasurableSet (A i))
    (Ω : Set X) (hΩ : IsOpen Ω) (hΩn : Ω.Nonempty)
    (hCover : Ω ⊆ ⋃ i, A i) :
    ∃ i, ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
      ∀ᶠ x in residual X, x ∈ U → x ∈ A i := by
  classical
  have hNon : ∃ i, ¬ IsMeagre (Ω ∩ A i) := by
    by_contra! h
    apply not_isMeagre_of_isOpen hΩ hΩn
    apply (isMeagre_iUnion h).mono
    intro x hxΩ
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover hxΩ)
    exact mem_iUnion.mpr ⟨i, hxΩ, hi⟩
  obtain ⟨i, hi⟩ := hNon
  obtain ⟨V, hVo, hEq⟩ := (hΩ.baireMeasurableSet.inter (hA i)).residualEq_isOpen
  have hEq' : ∀ᶠ x in residual X, x ∈ Ω ∩ A i ↔ x ∈ V :=
    Filter.eventuallyEq_set.mp hEq
  have hVn : V.Nonempty := by
    by_contra hn
    have hVe : V = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hi
    filter_upwards [hEq'] with x hx
    simpa [hVe] using hx
  obtain ⟨x, hxV, hxEq⟩ := (dense_of_mem_residual hEq').inter_open_nonempty V hVo hVn
  have hxΩ := ((hxEq.mpr hxV).1)
  refine ⟨i, V ∩ Ω, hVo.inter hΩ, ⟨x, hxV, hxΩ⟩, inter_subset_right, ?_⟩
  filter_upwards [hEq'] with y hy
  intro hyU
  exact (hy.mpr hyU.1).2

/-- Restricting an ambient comeager assertion to an open subspace preserves
comeagerness. -/
theorem eventually_residual_open_subspace (U : Set X) (hU : IsOpen U)
    {P : X → Prop} (hP : ∀ᶠ x in residual X, P x) :
    ∀ᶠ x : U in residual U, P (x : X) :=
  tendsto_residual_of_isOpenMap continuous_subtype_val hU.isOpenMap_subtype_val hP

/-- A residual assertion on an open subspace is the same as an ambient
residual implication on that open set. -/
theorem eventually_residual_of_open_subspace (U : Set X) (_hU : IsOpen U)
    {P : X → Prop} (hP : ∀ᶠ x : U in residual U, P (x : X)) :
    ∀ᶠ x in residual X, x ∈ U → P x := by
  classical
  have hm : IsMeagre {x : U | ¬ P (x : X)} := by
    simpa only [IsMeagre, compl_setOf, not_not] using hP
  have hImage : IsMeagre ((↑) '' {x : U | ¬ P (x : X)} : Set X) := hm.image_val
  filter_upwards [hImage] with x hx hxU
  by_contra hxP
  exact hx ⟨⟨x, hxU⟩, hxP, rfl⟩

#print axioms baire_cover_local_residual

end BenchmarkJump
