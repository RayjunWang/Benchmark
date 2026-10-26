import MeasureRowCover
import ContinuousSquareReweight

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

abbrev PositiveContinuousWeight := {w : C(HaarCantor, ℝ) | ∀ x, 0 < w x}

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish

/-- Category consequence of the concrete positive continuous reweight
homeomorphisms. The orbit-density premise is a separately tracked remaining
dependency, to be discharged by finite-prefix mass matching. -/
theorem fullSupportMeasureEquivalence_genericallyErgodic_of_dense_reweights
    (hDense : ∀ μ : PositiveCylinderProbabilities,
      Dense (range (fun w : PositiveContinuousWeight => continuousSquareReweight w.1 w.property μ))) :
    GenericallyErgodic FullSupportMeasureEquivalence := by
  classical
  intro A hA hInv
  by_cases hm : IsMeagre A
  · exact Or.inl hm
  right
  obtain ⟨U, hUo, hAU⟩ := hA.residualEq_isOpen
  have hAU' : ∀ᶠ x in residual PositiveCylinderProbabilities, x ∈ A ↔ x ∈ U :=
    Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra hn
    have hUe : U = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hm
    filter_upwards [hAU'] with x hx
    simp [hUe] at hx
    exact hx
  have hMove (x : PositiveCylinderProbabilities) : ∃ w : PositiveContinuousWeight,
      continuousSquareReweight w.1 w.property x ∈ U := by
    obtain ⟨y, hyU, hyRange⟩ := (hDense x).inter_open_nonempty U hUo hUne
    obtain ⟨w, rfl⟩ := hyRange
    exact ⟨w, hyU⟩
  choose w hmem using hMove
  let V : PositiveCylinderProbabilities → Set PositiveCylinderProbabilities :=
    fun x => {y | continuousSquareReweight (w x).1 (w x).property y ∈ U}
  have hVnhds (x : PositiveCylinderProbabilities) : V x ∈ 𝓝 x :=
    (hUo.preimage (continuous_continuousSquareReweight _ _)).mem_nhds (hmem x)
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hVnhds
  have hAll : ∀ᶠ y in residual PositiveCylinderProbabilities, ∀ x ∈ S,
      continuousSquareReweight (w x).1 (w x).property y ∈ A ↔
        continuousSquareReweight (w x).1 (w x).property y ∈ U := by
    apply eventually_countable_ball hScount |>.2
    intro x _hx
    exact tendsto_residual_of_isOpenMap (continuous_continuousSquareReweight _ _)
      (continuousSquareReweightHomeomorph _ _).isOpenMap hAU'
  filter_upwards [hAll] with y hy
  have hyCover : y ∈ ⋃ x ∈ S, V x := by rw [hScover]; trivial
  obtain ⟨x, hx⟩ := mem_iUnion.mp hyCover
  obtain ⟨hxS, hyV⟩ := mem_iUnion.mp hx
  have hyA := (hy x hxS).mpr hyV
  exact (hInv y (continuousSquareReweight (w x).1 (w x).property y)
    (densitySource_target_equivalent (positiveContinuousSection (w x).1 (w x).property y))).mpr hyA

#print axioms fullSupportMeasureEquivalence_genericallyErgodic_of_dense_reweights

end BenchmarkJump
