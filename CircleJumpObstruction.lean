import CircleInterpolationChain

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable
local instance : MeasurableSpace NullCircleGroup := borel NullCircleGroup
local instance : BorelSpace NullCircleGroup := ⟨rfl⟩
local instance : MeasurableSpace CircleSequences := borel CircleSequences
local instance : BorelSpace CircleSequences := ⟨rfl⟩

/-- The actual local row property for every Borel jump homomorphism out of
compact-circle null difference. All analytic and category hypotheses are
discharged by the preceding modules. -/
theorem circle_local_rows
    (F : CircleSequences → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism CircleNullDifference (Jump BoundedDifference) F) :
    LocallyGenericallyConstantRows BoundedDifference F := by
  intro k A hAo hAn
  obtain ⟨l, n, U, W, hUo, hUn, hWo, hWn, hRect, hRes⟩ :=
    circle_row_match_rectangle F hFm hF k A hAo hAn
  obtain ⟨h₀, hh₀⟩ := hWn
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hWo h₀ hh₀
  let f : CircleSequences → RealSequences := fun x => F x k
  let g : CircleSequences → RealSequences := fun x => F x l
  obtain ⟨D, hDG, _hDd, hf⟩ := measurable_continuousOn_residual f
    ((measurable_pi_apply k).comp hFm)
  have hD : D ∈ residual CircleSequences := residual_of_dense_Gδ hDG _hDd
  let Ω : Set CircleSequences :=
    (fun x : CircleSequences => x + nullCircleCoordinates h₀) '' U
  have hΩo : IsOpen Ω := isOpenMap_add_right (nullCircleCoordinates h₀) _ hUo
  have hΩn : Ω.Nonempty := hUn.image _
  have hΩA : Ω ⊆ A := by
    rintro y ⟨x, hxU, rfl⟩
    exact hRect (show (x, h₀) ∈ U ×ˢ W from ⟨hxU, hh₀⟩)
  have hVn : (circleChart ⁻¹' Ω).Nonempty := by
    obtain ⟨y, hyΩ, hyRange⟩ := denseRange_circleChart.inter_open_nonempty Ω hΩo hΩn
    obtain ⟨x, rfl⟩ := hyRange
    exact ⟨x, hyΩ⟩
  obtain ⟨C, hCo, hCn, hCV, hC⟩ := exists_open_chartConvex_subset
    (circleChart ⁻¹' Ω) (hΩo.preimage continuous_circleChart) hVn
  have hSmall : ∀ y ∈ circleChart '' C, ∀ z ∈ circleChart '' C,
      y ∈ D → z ∈ D → ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      (∀ i, ‖z i - y i‖ ≤ δ) → BoundedDifference (f y) (f z) := by
    intro y hyC z _hzC hyD hzD δ hδ hδε hSmall
    have hyΩ : y ∈ Ω := by
      obtain ⟨cy, hcy, rfl⟩ := hyC
      exact hCV hcy
    obtain ⟨x, hxU, hxy⟩ := hyΩ
    have hxy' : circleAction (x, h₀) = y := hxy
    refine ⟨2 * n, ?_⟩
    have hb := circle_small_pair_bound U W hUo hWo D hD f g hf n hRes
      h₀ hh₀ ε hBall x z hxU (hxy'.symm ▸ hyD) hzD δ hδ hδε
      (fun i => by simpa only [hxy'] using hSmall i)
    simpa only [hxy'] using hb
  obtain ⟨a, ha⟩ := circle_interpolation_constant_on_chart C hCo hCn hC D hD f ε hε hSmall
  obtain ⟨O, hOo, hOn, hOA, hConst⟩ := circleChart_local_constancy A hAo C hCo hCn
    (fun x hx => hΩA (hCV hx)) (fun y => BoundedDifference (f y) a) ha
  exact ⟨O, a, hOo, hOn, hOA, hConst⟩

/-- No Borel reduction of actual compact-circle null difference to the
Friedman--Stanley jump of actual bounded difference exists. -/
theorem circle_null_not_borel_reducible_to_jump :
    ¬ ∃ F : CircleSequences → ℕ → RealSequences, Measurable F ∧
      ∀ x y, CircleNullDifference x y ↔ Jump BoundedDifference (F x) (F y) :=
  not_borel_reduction_of_local_rows CircleNullDifference BoundedDifference
    boundedDifference_equivalence measurableSet_boundedDifference
    circleNullDifference_genericallyErgodic circleNullDifference_class_meagre
    circle_local_rows

/-- The c0 half of Theorem1.4: the usual real null-difference relation is
not Borel reducible to the Friedman--Stanley jump of bounded difference. -/
theorem c0_not_borel_reducible_to_boundedDifferenceJump :
    ¬ ∃ F : RealSequences → ℕ → RealSequences, Measurable F ∧
      ∀ x y, Tendsto (fun i => x i - y i) atTop (𝓝 0) ↔
        Jump BoundedDifference (F x) (F y) := by
  rintro ⟨F, hFm, hRed⟩
  apply circle_null_not_borel_reducible_to_jump
  refine ⟨F ∘ MeasureEquivalenceCircleReduction.realEmbed,
    hFm.comp MeasureEquivalenceCircleReduction.continuous_realEmbed.measurable, ?_⟩
  intro x y
  exact (MeasureEquivalenceCircleReduction.circle_real_null_reduction x y).trans
    (hRed (MeasureEquivalenceCircleReduction.realEmbed x)
      (MeasureEquivalenceCircleReduction.realEmbed y))

#print axioms circle_local_rows
#print axioms circle_null_not_borel_reducible_to_jump
#print axioms c0_not_borel_reducible_to_boundedDifferenceJump

end BenchmarkJump
