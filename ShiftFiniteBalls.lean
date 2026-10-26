import ShiftGraph
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact bounded-ball enumeration by padded words over the four signed
generators and the identity. No freeness of the action is assumed. -/

noncomputable section

namespace BenchmarkShift

def step (a : Alphabet) (x : Point) : Point :=
  match a with
  | none => x
  | some b => shift (letterGroup b) x

theorem continuous_step (a : Alphabet) : Continuous (step a) := by
  cases a with
  | none => exact continuous_id
  | some a => exact continuous_shift _

lemma step_reachable_dist (a : Alphabet) (x : Point) :
    graph.Reachable x (step a x) ∧ graph.dist x (step a x) ≤ 1 := by
  cases a with
  | none => exact ⟨SimpleGraph.Reachable.rfl, by simp [step]⟩
  | some a =>
      refine ⟨reachable_letter a x, ?_⟩
      by_cases h : x = shift (letterGroup a) x
      · simp only [step, ← h, SimpleGraph.dist_self, Nat.zero_le]
      · have ha : graph.Adj x (shift (letterGroup a) x) := ⟨h, a, rfl⟩
        exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr ha)

def wordMap : (r : ℕ) → (Fin r → Alphabet) → Point → Point
  | 0, _, x => x
  | r + 1, w, x => wordMap r (fun i => w i.succ) (step (w 0) x)

theorem continuous_wordMap (r : ℕ) (w : Fin r → Alphabet) : Continuous (wordMap r w) := by
  induction r with
  | zero => exact continuous_id
  | succ r ih => exact (ih (fun i => w i.succ)).comp (continuous_step (w 0))

lemma wordMap_none (r : ℕ) (x : Point) : wordMap r (fun _ => none) x = x := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [wordMap, step] using ih

lemma wordMap_reachable_dist (r : ℕ) (w : Fin r → Alphabet) (x : Point) :
    graph.Reachable x (wordMap r w x) ∧ graph.dist x (wordMap r w x) ≤ r := by
  induction r generalizing x with
  | zero => exact ⟨SimpleGraph.Reachable.rfl, by simp [wordMap]⟩
  | succ r ih =>
      have hfirst := step_reachable_dist (w 0) x
      have hrest := ih (fun i => w i.succ) (step (w 0) x)
      refine ⟨hfirst.1.trans hrest.1, ?_⟩
      have htri := hfirst.1.dist_triangle_left (wordMap r (fun i => w i.succ) (step (w 0) x))
      change graph.dist x (wordMap r (fun i => w i.succ) (step (w 0) x)) ≤ r + 1
      omega

lemma exists_word_of_distance (r : ℕ) : ∀ x y : Point,
    graph.Reachable x y → graph.dist x y ≤ r → ∃ w : Fin r → Alphabet, wordMap r w x = y := by
  induction r with
  | zero =>
      intro x y hr hd
      have hxy := hr.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hd)
      subst y
      exact ⟨fun i => Fin.elim0 i, rfl⟩
  | succ r ih =>
      intro x y hr hd
      obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
      cases w with
      | nil => exact ⟨fun _ => none, wordMap_none _ _⟩
      | @cons u v z hadj w =>
          obtain ⟨a, ha⟩ := hadj.2
          have hlen : w.length ≤ r := by
            simp only [SimpleGraph.Walk.length_cons] at hw
            omega
          obtain ⟨rest, hrest⟩ := ih v y ⟨w⟩ ((SimpleGraph.dist_le w).trans hlen)
          refine ⟨Fin.cons (some a) rest, ?_⟩
          simpa only [wordMap, Fin.cons_zero, Fin.cons_succ, step, ha] using hrest

def ballSize (r : ℕ) : ℕ := Fintype.card (Fin r → Alphabet)

def ball (r : ℕ) (i : Fin (ballSize r)) : Point → Point :=
  wordMap r ((Fintype.equivFin (Fin r → Alphabet)).symm i)

theorem measurable_ball (r : ℕ) (i : Fin (ballSize r)) : Measurable (ball r i) :=
  (continuous_wordMap r _).measurable

theorem ball_complete (r : ℕ) (x z : Point) :
    (graph.Reachable x z ∧ graph.dist x z ≤ r) ↔ ∃ i, ball r i x = z := by
  constructor
  · rintro ⟨hr, hd⟩
    obtain ⟨w, hw⟩ := exists_word_of_distance r x z hr hd
    refine ⟨Fintype.equivFin (Fin r → Alphabet) w, ?_⟩
    simpa only [ball, Equiv.symm_apply_apply] using hw
  · rintro ⟨i, rfl⟩
    exact wordMap_reachable_dist r _ x

end BenchmarkShift

#print axioms BenchmarkShift.ball_complete
