import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-! A Borel greedy finite coloring, from an explicitly enumerated finite
neighbor family and a countable Borel proper coloring. This supplies the
finite-coloring step needed by the graph-distance block construction. -/

noncomputable section

namespace BenchmarkFiniteColoring

lemma exists_missing (d : ℕ) (a : Fin d → Fin (d + 1)) :
    ∃ c : Fin (d + 1), ∀ i, c ≠ a i := by
  classical
  have hns : ¬ Function.Surjective a := by
    intro hs
    have hcard := Fintype.card_le_of_surjective a hs
    simp only [Fintype.card_fin] at hcard
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨c, hc⟩ := hns
  exact ⟨c, fun i h => hc i h.symm⟩

def missing (d : ℕ) (a : Fin d → Fin (d + 1)) : Fin (d + 1) :=
  Classical.choose (exists_missing d a)

lemma missing_ne (d : ℕ) (a : Fin d → Fin (d + 1)) (i : Fin d) :
    missing d a ≠ a i := (Classical.choose_spec (exists_missing d a)) i

variable {X : Type*} (d : ℕ) (nb : Fin d → X → X) (rank : X → ℕ)

def stage : ℕ → X → Fin (d + 1)
  | 0 => fun _ => 0
  | n + 1 => fun x => if rank x = n then
      missing d (fun i => stage n (nb i x)) else stage n x

def finiteColor (x : X) : Fin (d + 1) := stage d nb rank (rank x + 1) x

lemma stage_stable (x : X) (n : ℕ) (hn : rank x + 1 ≤ n) :
    stage d nb rank n x = finiteColor d nb rank x := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hne : rank x ≠ n := by omega
      simpa only [stage, if_neg hne] using ih

lemma finiteColor_eq_missing (x : X) :
    finiteColor d nb rank x =
      missing d (fun i => stage d nb rank (rank x) (nb i x)) := by
  simp [finiteColor, stage]

theorem finiteColor_ne_of_rank_lt (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    {x y : X} (hxy : G.Adj x y) (hrank : rank x < rank y) :
    finiteColor d nb rank x ≠ finiteColor d nb rank y := by
  obtain ⟨i, hi⟩ := henum y x hxy.symm
  intro heq
  have hneq := missing_ne d (fun j => stage d nb rank (rank y) (nb j y)) i
  rw [hi, stage_stable d nb rank x (rank y) (by omega)] at hneq
  rw [← finiteColor_eq_missing] at hneq
  exact hneq heq.symm

theorem finiteColor_proper (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    (hproper : ∀ x y, G.Adj x y → rank x ≠ rank y) :
    ∀ x y, G.Adj x y → finiteColor d nb rank x ≠ finiteColor d nb rank y := by
  intro x y hxy
  rcases lt_or_gt_of_ne (hproper x y hxy) with hr | hr
  · exact finiteColor_ne_of_rank_lt d nb rank G henum hxy hr
  · exact (finiteColor_ne_of_rank_lt d nb rank G henum hxy.symm hr).symm

variable [MeasurableSpace X]

theorem measurable_stage
    (hnb : ∀ i, Measurable (nb i)) (hrank : Measurable rank) :
    ∀ n, Measurable (stage d nb rank n) := by
  classical
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hm : Measurable (fun x => missing d (fun i => stage d nb rank n (nb i x))) := by
        have ht : Measurable (fun x => fun i => stage d nb rank n (nb i x)) :=
          measurable_pi_lambda _ (fun i => ih.comp (hnb i))
        exact (measurable_of_countable (f := missing d)).comp ht
      exact hm.ite (measurableSet_eq_fun hrank measurable_const) ih

theorem measurable_finiteColor
    (hnb : ∀ i, Measurable (nb i)) (hrank : Measurable rank) :
    Measurable (finiteColor d nb rank) := by
  have hm : Measurable (fun p : ℕ × X => stage d nb rank p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_stage d nb rank hnb hrank)
  exact hm.comp ((hrank.add_const 1).prodMk measurable_id)

theorem exists_measurable_finite_proper_coloring (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    (hnb : ∀ i, Measurable (nb i)) (hrank : Measurable rank)
    (hproper : ∀ x y, G.Adj x y → rank x ≠ rank y) :
    ∃ c : X → Fin (d + 1), Measurable c ∧ ∀ x y, G.Adj x y → c x ≠ c y :=
  ⟨finiteColor d nb rank, measurable_finiteColor d nb rank hnb hrank,
    finiteColor_proper d nb rank G henum hproper⟩

end BenchmarkFiniteColoring

#print axioms BenchmarkFiniteColoring.exists_measurable_finite_proper_coloring
