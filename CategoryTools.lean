import JumpRows
import Mathlib.Topology.Baire.CompleteMetrizable

/-! Category tools needed by the concrete jump-obstruction arguments. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A Borel map into a second-countable space is continuous on a dense
Gdelta subspace of any Baire domain. This is relative continuity. -/
theorem measurable_continuousOn_residual
    [BaireSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    ∃ D : Set X, IsGδ D ∧ Dense D ∧ ContinuousOn f D := by
  classical
  have hB (B : countableBasis Y) :
      BaireMeasurableSet (f ⁻¹' (B : Set Y)) :=
    (hf (isOpen_of_mem_countableBasis B.property).measurableSet).baireMeasurableSet
  choose U hU hEq using fun B : countableBasis Y => (hB B).residualEq_isOpen
  have hAll : ∀ᶠ x in residual X, ∀ B : countableBasis Y,
      f x ∈ (B : Set Y) ↔ x ∈ U B :=
    eventually_countable_forall.2 fun B => Filter.eventuallyEq_set.mp (hEq B)
  obtain ⟨D, hDG, hDd, hD⟩ := eventually_residual.mp hAll
  refine ⟨D, hDG, hDd, (isBasis_countableBasis Y).continuousOn_iff.mpr ?_⟩
  intro B hB
  refine ⟨U ⟨B, hB⟩, hU _, ?_⟩
  ext x
  constructor
  · rintro ⟨hxB, hxD⟩
    exact ⟨(hD x hxD ⟨B, hB⟩).mp hxB, hxD⟩
  · rintro ⟨hxU, hxD⟩
    exact ⟨(hD x hxD ⟨B, hB⟩).mpr hxU, hxD⟩

/-- The projection of an open relation intersected with a nonempty open
vertical set is open. -/
theorem isOpen_exists_vertical {U : Set (X × Y)} (hU : IsOpen U)
    {V : Set Y} (hV : IsOpen V) :
    IsOpen {x | ∃ y ∈ V, (x, y) ∈ U} := by
  have heq : {x | ∃ y ∈ V, (x, y) ∈ U} =
      Prod.fst '' (U ∩ Prod.snd ⁻¹' V) := by
    ext x
    constructor
    · rintro ⟨y, hyV, hxy⟩
      exact ⟨(x, y), ⟨hxy, hyV⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hxy, hyV⟩, hxx⟩
      change x' = x at hxx
      subst x'
      exact ⟨y, hyV, hxy⟩
  rw [heq]
  exact isOpenMap_fst _ (hU.inter (hV.preimage continuous_snd))

/-- The same projection is dense when the relation is open dense and the
vertical set is nonempty open. -/
theorem dense_exists_vertical {U : Set (X × Y)} (hUd : Dense U)
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    Dense {x | ∃ y ∈ V, (x, y) ∈ U} := by
  apply dense_iff_inter_open.mpr
  intro A hAo hAn
  obtain ⟨x, hx⟩ := hAn
  obtain ⟨y, hy⟩ := hVn
  obtain ⟨⟨x', y'⟩, ⟨hxA, hyV⟩, hxyU⟩ :=
    hUd.inter_open_nonempty (A ×ˢ V) (hAo.prod hVo) ⟨(x, y), hx, hy⟩
  exact ⟨x', hxA, y', hyV, hxyU⟩

/-- The residual-set direction of Kuratowski--Ulam, proved from countable
bases and dense open projections. This suffices for the manuscript's use. -/
theorem eventually_residual_prod [SecondCountableTopology Y]
    {P : X × Y → Prop} (hP : ∀ᶠ p in residual (X × Y), P p) :
    ∀ᶠ x in residual X, ∀ᶠ y in residual Y, P (x, y) := by
  classical
  obtain ⟨S, hSo, hSd, hSc, hS⟩ := mem_residual_iff.mp hP
  letI : Countable S := hSc.to_subtype
  have hAll : ∀ᶠ x in residual X, ∀ U : S, ∀ B : countableBasis Y,
      ∃ y ∈ (B : Set Y), (x, y) ∈ (U : Set (X × Y)) := by
    apply eventually_countable_forall.mpr
    intro U
    apply eventually_countable_forall.mpr
    intro B
    exact residual_of_dense_open
      (isOpen_exists_vertical (hSo U U.property)
        (isOpen_of_mem_countableBasis B.property))
      (dense_exists_vertical (hSd U U.property)
        (isOpen_of_mem_countableBasis B.property)
        (nonempty_of_mem_countableBasis B.property))
  filter_upwards [hAll] with x hx
  have hFiber (U : S) : {y : Y | (x, y) ∈ (U : Set (X × Y))} ∈ residual Y := by
    apply residual_of_dense_open
    · exact (hSo U U.property).preimage (continuous_const.prodMk continuous_id)
    · apply dense_iff_inter_open.mpr
      intro V hVo hVn
      obtain ⟨y, hyV⟩ := hVn
      obtain ⟨B, hB, _hyB, hBV⟩ :=
        (isBasis_countableBasis Y).exists_subset_of_mem_open hyV hVo
      obtain ⟨z, hzB, hzx⟩ := hx U ⟨B, hB⟩
      exact ⟨z, hBV hzB, hzx⟩
  have hAllFiber : ∀ᶠ y in residual Y, ∀ U : S, (x, y) ∈ (U : Set (X × Y)) :=
    eventually_countable_forall.mpr hFiber
  filter_upwards [hAllFiber] with y hy
  exact hS (by intro U hU; exact hy ⟨U, hU⟩)

/-- An immediate version with an actual section: a comeager set of pairs
has a comeager vertical section in a nonempty Baire first factor. -/
theorem exists_residual_section [BaireSpace X] [Nonempty X]
    [SecondCountableTopology Y] {P : X × Y → Prop}
    (hP : ∀ᶠ p in residual (X × Y), P p) :
    ∃ x, ∀ᶠ y in residual Y, P (x, y) :=
  (dense_of_mem_residual (eventually_residual_prod hP)).nonempty

#print axioms measurable_continuousOn_residual
#print axioms eventually_residual_prod

end BenchmarkJump
