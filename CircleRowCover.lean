import BoundedDifferenceJump
import CategoryLocal
import CircleCategory
import CircleTopology
import Mathlib.Topology.Constructions.SumProd

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

abbrev NullCircleGroup := H0

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable
local instance : MeasurableSpace NullCircleGroup := borel NullCircleGroup
local instance : BorelSpace NullCircleGroup := ⟨rfl⟩
local instance : MeasurableSpace CircleSequences := borel CircleSequences
local instance : BorelSpace CircleSequences := ⟨rfl⟩

def nullCircleCoordinates (h : NullCircleGroup) : CircleSequences :=
  ((h : Hp ⊤) : CircleSequences)

theorem continuous_nullCircleCoordinates : Continuous nullCircleCoordinates :=
  continuous_h0_coordinates

def circleAction (p : CircleSequences × NullCircleGroup) : CircleSequences :=
  p.1 + nullCircleCoordinates p.2

theorem continuous_circleAction : Continuous circleAction :=
  continuous_fst.add (continuous_nullCircleCoordinates.comp continuous_snd)

/-- Endpoint maps of the actual circle null-group action are open. -/
theorem isOpenMap_circleAction : IsOpenMap circleAction := by
  intro W hW
  have heq : circleAction '' W = ⋃ h : NullCircleGroup,
      (fun x : CircleSequences => x + nullCircleCoordinates h) ''
        {x | (x, h) ∈ W} := by
    ext y
    constructor
    · rintro ⟨⟨x, h⟩, hxh, rfl⟩
      exact mem_iUnion.mpr ⟨h, x, hxh, rfl⟩
    · intro hy
      obtain ⟨h, x, hxh, hxy⟩ := mem_iUnion.mp hy
      exact ⟨(x, h), hxh, hxy⟩
  rw [heq]
  apply isOpen_iUnion
  intro h
  exact isOpenMap_add_right (nullCircleCoordinates h) _
    (hW.preimage (continuous_id.prodMk continuous_const))

theorem circleAction_null_related (p : CircleSequences × NullCircleGroup) :
    CircleNullDifference p.1 (circleAction p) := by
  have hh : Tendsto (fun n => nullCircleCoordinates p.2 n) atTop (𝓝 0) := p.2.property
  simpa [CircleNullDifference, MeasureEquivalenceCircleReduction.CircleNullRel,
    circleAction, nullCircleCoordinates] using hh.neg

/-- The concrete Baire cover step of the c0 jump proof: on one nonempty
rectangle a fixed output row matches a fixed input row with one uniform bound. -/
theorem circle_row_match_rectangle
    (F : CircleSequences → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism CircleNullDifference (Jump BoundedDifference) F)
    (k : ℕ) (A : Set CircleSequences) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ l n : ℕ, ∃ U : Set CircleSequences, ∃ W : Set NullCircleGroup,
      IsOpen U ∧ U.Nonempty ∧ IsOpen W ∧ W.Nonempty ∧
      U ×ˢ W ⊆ circleAction ⁻¹' A ∧
      ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
        p ∈ U ×ˢ W → UniformBound n (F (circleAction p) k) (F p.1 l) := by
  classical
  let B : ℕ × ℕ → Set (CircleSequences × NullCircleGroup) := fun i =>
    {p | UniformBound i.2 (F (circleAction p) k) (F p.1 i.1)}
  have hB (i : ℕ × ℕ) : BaireMeasurableSet (B i) := by
    apply MeasurableSet.baireMeasurableSet
    exact (isClosed_uniformBound i.2).measurableSet.preimage
      (((measurable_pi_apply k).comp (hFm.comp continuous_circleAction.measurable)).prodMk
        ((measurable_pi_apply i.1).comp (hFm.comp measurable_fst)))
  let Ω : Set (CircleSequences × NullCircleGroup) := circleAction ⁻¹' A
  have hΩo : IsOpen Ω := hAo.preimage continuous_circleAction
  have hΩn : Ω.Nonempty := by
    obtain ⟨x, hx⟩ := hAn
    refine ⟨(x, 0), ?_⟩
    have heq : circleAction (x, 0) = x := by
      ext n
      change x n + 0 = x n
      exact add_zero _
    change circleAction (x, 0) ∈ A
    rw [heq]
    exact hx
  have hCover : Ω ⊆ ⋃ i, B i := by
    intro p _hp
    obtain ⟨l, hl⟩ := (hF p.1 (circleAction p) (circleAction_null_related p)).2 k
    obtain ⟨n, hn⟩ := boundedDifference_equivalence.symm hl
    exact mem_iUnion.mpr ⟨(l, n), hn⟩
  obtain ⟨i, V, hVo, hVn, hVΩ, hVres⟩ :=
    baire_cover_local_residual B hB Ω hΩo hΩn hCover
  obtain ⟨⟨x, h⟩, hxh⟩ := hVn
  obtain ⟨U, W, hUo, hWo, hxU, hhW, hUW⟩ := isOpen_prod_iff.mp hVo x h hxh
  refine ⟨i.1, i.2, U, W, hUo, ⟨x, hxU⟩, hWo, ⟨h, hhW⟩,
    hUW.trans hVΩ, ?_⟩
  filter_upwards [hVres] with p hp hpUW
  exact hp (hUW hpUW)

#print axioms circle_row_match_rectangle
#print axioms isOpenMap_circleAction

end BenchmarkJump
