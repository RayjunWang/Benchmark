import ShiftGraph
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! First-letter cone cancellation for the free group on two generators.
Left multiplication by a letter sends the complement of its inverse
cone bijectively onto its own cone. -/

open Set

noncomputable section

namespace BenchmarkShift

def cone (a : Letter) : Set Group := {g | g.toWord.head? = some a}

lemma letterGroup_eq_mk (a : Letter) : letterGroup a = FreeGroup.mk [a] := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [letterGroup, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

lemma toWord_letter_mul (a : Letter) (g : Group) :
    (letterGroup a * g).toWord = FreeGroup.reduce (a :: g.toWord) := by
  rw [letterGroup_eq_mk, ← FreeGroup.mk_toWord (x := g), FreeGroup.mul_mk, FreeGroup.toWord_mk]
  simp only [List.singleton_append, FreeGroup.toWord_mk, FreeGroup.reduce_toWord]

lemma cancellation_iff_reverse (a b : Letter) :
    (a.1 = b.1 ∧ a.2 = !b.2) ↔ b = reverseLetter a := by
  rcases a with ⟨i, ab⟩
  rcases b with ⟨j, bb⟩
  cases ab <;> cases bb <;> simp [reverseLetter, Prod.ext_iff, eq_comm]

lemma not_reduced_reverse_cons (a : Letter) (L : List Letter) :
    ¬ FreeGroup.IsReduced (reverseLetter a :: a :: L) := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [reverseLetter, FreeGroup.isReduced_cons_cons]

theorem cone_letter_mul_iff (a : Letter) (g : Group) :
    letterGroup a * g ∈ cone a ↔ g ∉ cone (reverseLetter a) := by
  unfold cone
  simp only [mem_setOf_eq]
  rw [toWord_letter_mul, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases hw : g.toWord with
  | nil => simp
  | cons b L =>
      change (if a.1 = b.1 ∧ a.2 = !b.2 then L else a :: b :: L).head? = some a ↔
        (some b : Option Letter) ≠ some (reverseLetter a)
      by_cases hb : b = reverseLetter a
      · rw [if_pos ((cancellation_iff_reverse a b).mpr hb)]
        simp only [hb, ne_eq, not_true_eq_false, iff_false]
        intro hhead
        have hred : FreeGroup.IsReduced (b :: L) := by
          rw [← hw]
          exact FreeGroup.isReduced_toWord
        cases L with
        | nil => simp at hhead
        | cons c tail =>
            have hca : c = a := Option.some.inj hhead
            subst c
            rw [hb] at hred
            exact not_reduced_reverse_cons a tail hred
      · have hc : ¬ (a.1 = b.1 ∧ a.2 = !b.2) :=
          fun h => hb ((cancellation_iff_reverse a b).mp h)
        simp only [if_neg hc, List.head?_cons, true_iff, ne_eq, Option.some.injEq]
        exact hb

theorem cone_preimage_left (a : Letter) :
    (fun g : Group => letterGroup a * g) ⁻¹' cone a = (cone (reverseLetter a))ᶜ := by
  ext g
  exact cone_letter_mul_iff a g

theorem cone_disjoint {a b : Letter} (hab : a ≠ b) : Disjoint (cone a) (cone b) := by
  rw [Set.disjoint_left]
  intro g ha hb
  exact hab (Option.some.inj (ha.symm.trans hb))

end BenchmarkShift

#print axioms BenchmarkShift.cone_preimage_left
