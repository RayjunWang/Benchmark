import JumpRows
import CircleReduction
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Group.Basic

/-! The concrete category properties of null difference on the compact
product of circles. These are the source-side category hypotheses of the
first jump obstruction, proved here without assuming the obstruction. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

abbrev CircleSequences := ℕ → UnitAddCircle
abbrev CircleNullDifference := MeasureEquivalenceCircleReduction.CircleNullRel

def CircleTailBound (a : CircleSequences) (N : ℕ) : Set CircleSequences :=
  {x | ∀ n, N ≤ n → ‖x n - a n‖ ≤ (1 / 8 : ℝ)}

theorem isClosed_circleTailBound (a : CircleSequences) (N : ℕ) :
    IsClosed (CircleTailBound a N) := by
  change IsClosed {x : CircleSequences | ∀ n, N ≤ n → ‖x n - a n‖ ≤ (1 / 8 : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro _hn
  exact isClosed_le (((continuous_apply n).sub continuous_const).norm) continuous_const

theorem interior_circleTailBound (a : CircleSequences) (N : ℕ) :
    interior (CircleTailBound a N) = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp isOpen_interior x hx
  let n : ℕ := max N (I.sup id + 1)
  have hNn : N ≤ n := le_max_left _ _
  have hnI : n ∉ I := by
    intro hn
    have hle : n ≤ I.sup id := Finset.le_sup (f := id) hn
    have hlt : I.sup id < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    omega
  let y : CircleSequences := Function.update x n (a n + ((1 / 2 : ℝ) : UnitAddCircle))
  have hy : y ∈ (I : Set ℕ).pi V := by
    intro i hi
    have hin : i ≠ n := by intro h; exact hnI (h ▸ hi)
    simpa only [y, Function.update_of_ne hin] using (hV i hi).2
  have hbad := interior_subset (hVI hy) n hNn
  have hnorm : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = (1 / 2 : ℝ) := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  simp [y, hnorm] at hbad
  norm_num at hbad

theorem isNowhereDense_circleTailBound (a : CircleSequences) (N : ℕ) :
    IsNowhereDense (CircleTailBound a N) :=
  (isClosed_circleTailBound a N).isNowhereDense_iff.mpr (interior_circleTailBound a N)

/-- Every actual null-difference class in the compact circle product is meager. -/
theorem circleNullDifference_class_meagre (a : CircleSequences) :
    IsMeagre {x | CircleNullDifference x a} := by
  apply (isMeagre_iUnion (fun N => (isNowhereDense_circleTailBound a N).isMeagre)).mono
  intro x hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (1 / 8 : ℝ) (by norm_num)
  exact mem_iUnion.2 ⟨N, fun n hn => by simpa only [dist_zero_right] using (hN n hn).le⟩

def FinitelySupportedCircle (h : CircleSequences) : Prop :=
  ∃ I : Finset ℕ, ∀ n, n ∉ I → h n = 0

theorem circleNullDifference_translate (h : CircleSequences)
    (hh : FinitelySupportedCircle h) (x : CircleSequences) :
    CircleNullDifference x (x + h) := by
  obtain ⟨I, hI⟩ := hh
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (I.sup id)] with n hn
  have hnI : n ∉ I := by
    intro hi
    exact (not_le_of_gt hn) (Finset.le_sup (f := id) hi)
  simp [hI n hnI]

/-- Finite-coordinate translations can move each point into any prescribed
nonempty product-open set. -/
theorem finite_translate_into_open (U : Set CircleSequences)
    (hU : IsOpen U) (hne : U.Nonempty) (x : CircleSequences) :
    ∃ h : CircleSequences, FinitelySupportedCircle h ∧ x + h ∈ U := by
  classical
  obtain ⟨u, hu⟩ := hne
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp hU u hu
  let h : CircleSequences := fun i => if i ∈ I then u i - x i else 0
  refine ⟨h, ⟨I, fun n hn => by simp [h, hn]⟩, hVI ?_⟩
  intro i hi
  change i ∈ I at hi
  simpa [h, hi] using (hV i hi).2

/-- Generic ergodicity of the concrete compact-circle null-difference
relation. A countable open subcover is extracted from finite-coordinate
translations; no unproved countability of the whole translating group is used. -/
theorem circleNullDifference_genericallyErgodic :
    GenericallyErgodic CircleNullDifference := by
  classical
  intro A hA hInv
  by_cases hm : IsMeagre A
  · exact Or.inl hm
  right
  obtain ⟨U, hUo, hAU⟩ := hA.residualEq_isOpen
  have hAU' : ∀ᶠ x in residual CircleSequences, x ∈ A ↔ x ∈ U :=
    Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra hn
    have hUe : U = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hm
    filter_upwards [hAU'] with x hx
    simp [hUe] at hx
    exact hx
  choose h hh hmem using finite_translate_into_open U hUo hUne
  let V : CircleSequences → Set CircleSequences := fun x => {y | y + h x ∈ U}
  have hVnhds (x : CircleSequences) : V x ∈ 𝓝 x :=
    (hUo.preimage (continuous_id.add continuous_const)).mem_nhds (hmem x)
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hVnhds
  have hAll : ∀ᶠ y in residual CircleSequences, ∀ x ∈ S,
      y + h x ∈ A ↔ y + h x ∈ U := by
    apply eventually_countable_ball hScount |>.2
    intro x _hx
    exact tendsto_residual_of_isOpenMap
      (continuous_id.add continuous_const) (isOpenMap_add_right (h x)) hAU'
  filter_upwards [hAll] with y hy
  have hycover : y ∈ ⋃ x ∈ S, V x := by rw [hScover]; trivial
  obtain ⟨x, hx⟩ := mem_iUnion.1 hycover
  obtain ⟨hxS, hyV⟩ := mem_iUnion.1 hx
  have hyA : y + h x ∈ A := (hy x hxS).mpr hyV
  exact (hInv y (y + h x) (circleNullDifference_translate (h x) (hh x) y)).mpr hyA

#print axioms circleNullDifference_class_meagre
#print axioms circleNullDifference_genericallyErgodic

end BenchmarkJump
