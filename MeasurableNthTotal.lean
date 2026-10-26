import MeasureGramSchmidtBorel

/-! The total Nat.nth selector is Borel for arbitrary Borel predicates,
including finite and empty fibers. Out-of-range indices return zero. -/

open MeasureTheory Set

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem measurable_nat_nth_total (p : X → ℕ → Prop) [∀ x, DecidablePred (p x)]
    (hp : ∀ n, MeasurableSet {x | p x n}) (n : ℕ) :
    Measurable (fun x => Nat.nth (p x) n) := by
  have hnonzero (m : ℕ) (hm : m ≠ 0) :
      {x | Nat.nth (p x) n = m} = {x | p x m} ∩ {x | Nat.count (p x) m = n} := by
    ext x
    constructor
    · intro he
      have hne : Nat.nth (p x) n ≠ 0 := fun hz => hm (he.symm.trans hz)
      have hcard : ∀ hf : {k : ℕ | p x k}.Finite, n < hf.toFinset.card :=
        fun hf => Nat.lt_card_toFinset_of_nth_ne_zero hne hf
      exact ⟨he ▸ Nat.nth_mem n hcard, he ▸ Nat.count_nth hcard⟩
    · rintro ⟨hpm,hcount⟩
      rw [← hcount]
      exact Nat.nth_count hpm
  have hmeas (m : ℕ) (hm : m ≠ 0) : MeasurableSet {x | Nat.nth (p x) n = m} := by
    rw [hnonzero m hm]
    exact (hp m).inter (measurableSet_eq_fun (measurable_nat_count p hp m) measurable_const)
  apply measurable_to_countable'
  intro m
  by_cases hm : m = 0
  · subst m
    have heq : {x | Nat.nth (p x) n = 0} =
        (⋃ k : {i : ℕ // i ≠ 0}, {x | Nat.nth (p x) n = k.val})ᶜ := by
      ext x
      simp only [mem_setOf_eq, mem_compl_iff, mem_iUnion]
      constructor
      · intro hx
        rintro ⟨k,hk⟩
        exact k.property (hk.symm.trans hx)
      · intro hx
        by_contra hne
        exact hx ⟨⟨Nat.nth (p x) n,hne⟩,rfl⟩
    change MeasurableSet {x | Nat.nth (p x) n = 0}
    rw [heq]
    exact (MeasurableSet.iUnion (fun k : {i : ℕ // i ≠ 0} => hmeas k.val k.property)).compl
  · exact hmeas m hm

end
end MeasureUnitary

#print axioms MeasureUnitary.measurable_nat_nth_total
