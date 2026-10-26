import CategoryLocal
import ShiftNullReduction
import Definitions.Def_BenchmarkRelations
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Baire.CompleteMetrizable

/-! The actual real-sequence Lp translation action and the countable-orbit
Baire cover needed for the reverse countable benchmark obstruction. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

abbrev RealSequences := ℕ → ℝ
abbrev Translations (p : ℝ≥0∞) := lp (fun _ : ℕ => ℝ) p

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

local instance : MeasurableSpace (Translations p) := borel (Translations p)
local instance : BorelSpace (Translations p) := ⟨rfl⟩

def coordinates (h : Translations p) : RealSequences := h

lemma continuous_coordinates : Continuous (coordinates p) := lp.uniformContinuous_coe.continuous

def translationAction (a : RealSequences × Translations p) : RealSequences :=
  a.1 + coordinates p a.2

lemma continuous_translationAction : Continuous (translationAction p) :=
  continuous_fst.add ((continuous_coordinates p).comp continuous_snd)

lemma isOpenMap_translationAction : IsOpenMap (translationAction p) := by
  intro W hW
  have heq : translationAction p '' W = ⋃ h : Translations p,
      (fun x : RealSequences => x + coordinates p h) '' {x | (x, h) ∈ W} := by
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
  exact isOpenMap_add_right (coordinates p h) _
    (hW.preimage (continuous_id.prodMk continuous_const))

lemma translationAction_lp_related (hp : p ≠ ∞) (a : RealSequences × Translations p) :
    BenchmarkComparisons.LpDifference p.toReal a.1 (translationAction p a) := by
  have hs := (memℓp_gen_iff (p.toReal_pos_iff_ne_top.mpr hp)).mp (lp.memℓp a.2)
  simpa only [BenchmarkComparisons.LpDifference, translationAction, coordinates,
    Pi.add_apply, sub_add_cancel_left, abs_neg, Real.norm_eq_abs] using hs

theorem countable_orbit_rectangle (hp : p ≠ ∞)
    (f : RealSequences → BenchmarkShift.Point) (hf : Measurable f)
    (hF : ∀ x y, BenchmarkComparisons.LpDifference p.toReal x y →
      BenchmarkComparisons.EInfinity (f x) (f y)) :
    ∃ g : BenchmarkShift.Group, ∃ U : Set RealSequences, ∃ W : Set (Translations p),
      IsOpen U ∧ U.Nonempty ∧ IsOpen W ∧ W.Nonempty ∧
      ∀ᶠ a in residual (RealSequences × Translations p),
        a ∈ U ×ˢ W → f (translationAction p a) = BenchmarkShift.shift g (f a.1) := by
  classical
  let B : BenchmarkShift.Group → Set (RealSequences × Translations p) := fun g =>
    {a | f (translationAction p a) = BenchmarkShift.shift g (f a.1)}
  have hB (g : BenchmarkShift.Group) : BaireMeasurableSet (B g) := by
    apply MeasurableSet.baireMeasurableSet
    exact measurableSet_eq_fun (hf.comp (continuous_translationAction p).measurable)
      (((BenchmarkShift.continuous_shift g).measurable.comp hf).comp measurable_fst)
  have hcover : (univ : Set (RealSequences × Translations p)) ⊆ ⋃ g, B g := by
    intro a _
    obtain ⟨g, hg⟩ := hF a.1 (translationAction p a) (translationAction_lp_related p hp a)
    apply mem_iUnion.mpr
    refine ⟨g, ?_⟩
    exact funext hg
  obtain ⟨g, V, hVo, hVn, _hVU, hVres⟩ :=
    BenchmarkJump.baire_cover_local_residual B hB univ isOpen_univ univ_nonempty hcover
  obtain ⟨⟨x, h⟩, hxh⟩ := hVn
  obtain ⟨U, W, hUo, hWo, hxU, hhW, hUW⟩ := isOpen_prod_iff.mp hVo x h hxh
  refine ⟨g, U, W, hUo, ⟨x, hxU⟩, hWo, ⟨h, hhW⟩, ?_⟩
  filter_upwards [hVres] with a ha hrect
  exact ha (hUW hrect)

end BenchmarkCountableReverse

#print axioms BenchmarkCountableReverse.countable_orbit_rectangle
