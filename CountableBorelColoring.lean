import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic

/-! A countable Borel coloring for a finite family of Borel neighbor maps.
It is constructed from a Borel injection into Cantor space by taking the
first binary prefix that distinguishes the point from its distinct neighbors.
-/

noncomputable section

open Set

namespace BenchmarkCountableColoring

variable {X : Type*} (d : ℕ) (nb : Fin d → X → X) (code : X → ℕ → Bool)
  (hinj : Function.Injective code)

def distinguishes (x : X) (n : ℕ) : Prop :=
  ∀ i : Fin d, nb i x = x ∨ ∃ j : Fin n, code (nb i x) j ≠ code x j

include hinj

lemma exists_distinguishes (x : X) : ∃ n, distinguishes d nb code x n := by
  classical
  have hex : ∀ i : Fin d, ∃ n, nb i x = x ∨
      ∃ j : Fin n, code (nb i x) j ≠ code x j := by
    intro i
    by_cases hix : nb i x = x
    · exact ⟨0, Or.inl hix⟩
    · have hne : code (nb i x) ≠ code x := fun h => hix (hinj h)
      have : ∃ j : ℕ, code (nb i x) j ≠ code x j := by
        by_contra h
        push Not at h
        exact hne (funext h)
      obtain ⟨j, hj⟩ := this
      exact ⟨j + 1, Or.inr ⟨⟨j, by omega⟩, hj⟩⟩
  choose b hb using hex
  refine ⟨∑ i, b i, fun i => ?_⟩
  rcases hb i with h | ⟨j, hj⟩
  · exact Or.inl h
  · have hle : b i ≤ ∑ a, b a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Or.inr ⟨⟨j, lt_of_lt_of_le j.isLt hle⟩, hj⟩

def prefixLength (x : X) : ℕ := by
  classical
  exact Nat.find (exists_distinguishes d nb code hinj x)

lemma prefixLength_spec (x : X) :
    distinguishes d nb code x (prefixLength d nb code hinj x) := by
  classical
  exact Nat.find_spec (exists_distinguishes d nb code hinj x)

def countColor (x : X) : ℕ :=
  Nat.pair (prefixLength d nb code hinj x)
    (Encodable.encode (List.ofFn (fun j : Fin (prefixLength d nb code hinj x) => code x j)))

theorem countColor_proper (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y) :
    ∀ x y, G.Adj x y → countColor d nb code hinj x ≠ countColor d nb code hinj y := by
  intro x y hxy heq
  obtain ⟨i, hi⟩ := henum x y hxy
  have hp := prefixLength_spec d nb code hinj x i
  rw [hi] at hp
  rcases hp with hsame | ⟨j, hj⟩
  · exact hxy.ne hsame.symm
  · have hpair := Nat.pair_eq_pair.mp heq
    have hlen := hpair.1
    have hlist := Encodable.encode_injective hpair.2
    rw [← hlen] at hlist
    have hfun := List.ofFn_injective hlist
    have he := congrFun hfun j
    exact hj he.symm

variable [MeasurableSpace X]

theorem measurable_prefixLength
    (hnb : ∀ i, Measurable (nb i)) (hcode : Measurable code) :
    Measurable (prefixLength d nb code hinj) := by
  classical
  apply measurable_find
  intro n
  change MeasurableSet {x | ∀ i : Fin d, nb i x = x ∨
    ∃ j : Fin n, code (nb i x) j ≠ code x j}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have heq : MeasurableSet {x | nb i x = x} := by
    have he : MeasurableSet {x | code (nb i x) = code x} :=
      measurableSet_eq_fun (hcode.comp (hnb i)) hcode
    simpa only [hinj.eq_iff] using he
  have hneq : ∀ j : Fin n, MeasurableSet {x | code (nb i x) j ≠ code x j} := by
    intro j
    exact (measurableSet_eq_fun ((measurable_pi_apply (j : ℕ)).comp (hcode.comp (hnb i)))
      ((measurable_pi_apply (j : ℕ)).comp hcode)).compl
  simpa only [setOf_or, setOf_exists] using heq.union (MeasurableSet.iUnion hneq)

theorem measurable_countColor
    (hnb : ∀ i, Measurable (nb i)) (hcode : Measurable code) :
    Measurable (countColor d nb code hinj) := by
  have hm : Measurable (fun p : X × ℕ =>
      Nat.pair p.2 (Encodable.encode (List.ofFn (fun j : Fin p.2 => code p.1 j)))) := by
    apply measurable_from_prod_countable_left
    intro n
    have hp : Measurable (fun x => fun j : Fin n => code x j) :=
      measurable_pi_lambda _ (fun j => (measurable_pi_apply (j : ℕ)).comp hcode)
    exact (measurable_of_countable (fun f : Fin n → Bool =>
      Nat.pair n (Encodable.encode (List.ofFn f)))).comp hp
  exact hm.comp (measurable_id.prodMk (measurable_prefixLength d nb code hinj hnb hcode))

theorem exists_measurable_countable_proper_coloring (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    (hnb : ∀ i, Measurable (nb i)) (hcode : Measurable code) :
    ∃ c : X → ℕ, Measurable c ∧ ∀ x y, G.Adj x y → c x ≠ c y :=
  ⟨countColor d nb code hinj, measurable_countColor d nb code hinj hnb hcode,
    countColor_proper d nb code hinj G henum⟩

end BenchmarkCountableColoring

#print axioms BenchmarkCountableColoring.exists_measurable_countable_proper_coloring
