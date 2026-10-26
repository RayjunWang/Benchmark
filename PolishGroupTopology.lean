import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

/-!
Pettis category, Borel-homomorphism continuity, and uniqueness of compatible
Polish group topologies. This is a new standalone verification development.
-/

open Filter Set TopologicalSpace
open scoped Topology Pointwise

namespace MeasureEquivalenceTopology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BaireSpace G]

/-- Pettis's category lemma, proved from the property of Baire. -/
theorem pettis_nhds_one {A : Set G} (hA : BaireMeasurableSet A)
    (hnot : ¬ IsMeagre A) : A / A ∈ 𝓝 (1 : G) := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hprop : ∀ᵇ x, x ∈ A ↔ x ∈ U := Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra h
    have hzero : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    apply hnot
    change Aᶜ ∈ residual G
    filter_upwards [hprop] with x hx
    intro hxA
    have hxU := hx.mp hxA
    simp [hzero] at hxU
  obtain ⟨u, hu⟩ := hUne
  let W : Set G := {g | g⁻¹ * u ∈ U}
  have hW : W ∈ 𝓝 (1 : G) := by
    apply (hU.preimage (by fun_prop : Continuous (fun g : G => g⁻¹ * u))).mem_nhds
    simpa using hu
  apply Filter.mem_of_superset hW
  intro g hg
  have htrans : ∀ᵇ x, g⁻¹ * x ∈ A ↔ g⁻¹ * x ∈ U :=
    (tendsto_residual_of_isOpenMap
      (by fun_prop : Continuous (fun x : G => g⁻¹ * x))
      (isOpenMap_mul_left g⁻¹)) hprop
  let B : Set G := U ∩ (fun x : G => g⁻¹ * x) ⁻¹' U
  have hB : IsOpen B := hU.inter (hU.preimage (by fun_prop))
  have hBne : B.Nonempty := ⟨u, hu, hg⟩
  have hd : Dense {x : G | (x ∈ A ↔ x ∈ U) ∧
      (g⁻¹ * x ∈ A ↔ g⁻¹ * x ∈ U)} :=
    dense_of_mem_residual (hprop.and htrans)
  obtain ⟨x, hxB, hxR⟩ := hd.inter_open_nonempty B hB hBne
  refine Set.mem_div.mpr ⟨x, hxR.1.mpr hxB.1, g⁻¹ * x, hxR.2.mpr hxB.2, ?_⟩
  simp [div_eq_mul_inv]

/-- A Borel homomorphism from a Baire topological group to a second-countable
topological group is continuous. Neither surjectivity nor Polishness is needed. -/
theorem continuous_borel_hom [MeasurableSpace G] [BorelSpace G]
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (f : G →* L) (hf : Measurable f) : Continuous f := by
  apply continuous_of_tendsto_nhds_one f
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_split_inv hU
  obtain ⟨W, hWV, hWopen, hWone⟩ := mem_nhds_iff.mp hV
  let C : L → Set L := fun y => {z | z / y ∈ W}
  have hCopen (y : L) : IsOpen (C y) :=
    hWopen.preimage (by fun_prop : Continuous (fun z : L => z / y))
  have hCnhds (y : L) : C y ∈ 𝓝 y := (hCopen y).mem_nhds (by simpa [C])
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hCnhds
  have hcover : (⋃ y ∈ S, f ⁻¹' C y) = (Set.univ : Set G) := by
    have hpre := congrArg (fun T : Set L => f ⁻¹' T) hScover
    simpa only [Set.preimage_iUnion, Set.preimage_univ] using hpre
  have hnon : ∃ y ∈ S, ¬ IsMeagre (f ⁻¹' C y) := by
    by_contra h
    push Not at h
    have hmeagre := isMeagre_biUnion hScount h
    rw [hcover] at hmeagre
    exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hmeagre
  obtain ⟨y, _hyS, hy⟩ := hnon
  have hBP : BaireMeasurableSet (f ⁻¹' C y) :=
    (hf (hCopen y).measurableSet).baireMeasurableSet
  apply Filter.mem_of_superset (pettis_nhds_one hBP hy)
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_div.mp hz
  change f (a / b) ∈ U
  have haV : f a / y ∈ V := hWV ha
  have hbV : f b / y ∈ V := hWV hb
  have hh := hVV (f a / y) haV (f b / y) hbV
  simpa only [map_div, div_div_div_cancel_right] using hh

section Polish

variable [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
  {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [PolishSpace L] [MeasurableSpace L] [BorelSpace L]

/-- A Borel group isomorphism between Polish groups has Borel inverse by
Lusin--Souslin, and both directions are continuous by the category argument. -/
def borelGroupIsoHomeomorph (e : G ≃* L) (he : Measurable e) : G ≃ₜ L where
  toEquiv := e.toEquiv
  continuous_toFun := continuous_borel_hom e.toMonoidHom he
  continuous_invFun := by
    apply continuous_borel_hom e.symm.toMonoidHom
    apply (he.measurableEmbedding e.injective).measurable_comp_iff.mp
    change Measurable (fun x : L => e (e.symm x))
    have heq : (fun x : L => e (e.symm x)) = id := funext e.apply_symm_apply
    rw [heq]
    exact measurable_id

/-- Two Polish group presentations with the same continuous injective image
have the same topology under their algebraic identification. -/
def inclusionGroupIsoHomeomorph {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (i : G → X) (j : L → X) (hi : Continuous i) (hj : Continuous j)
    (hjinj : Function.Injective j) (e : G ≃* L) (he : ∀ x, j (e x) = i x) : G ≃ₜ L := by
  apply borelGroupIsoHomeomorph e
  apply (hj.measurableEmbedding hjinj).measurable_comp_iff.mp
  simpa only [Function.comp_def, he] using hi.measurable

end Polish

end MeasureEquivalenceTopology

#print axioms MeasureEquivalenceTopology.pettis_nhds_one
#print axioms MeasureEquivalenceTopology.continuous_borel_hom
#print axioms MeasureEquivalenceTopology.borelGroupIsoHomeomorph
#print axioms MeasureEquivalenceTopology.inclusionGroupIsoHomeomorph
