import FiberMultiplicityReflection
import MeasurableNthTotal
import Mathlib.Data.Set.Card

/-! A canonical Borel matching between equal-multiplicity counting
fibers, obtained by matching the preceding active-index counts. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem fiberMultiplicity_eq_encard (A : ℕ → Set X) (x : X) :
    fiberMultiplicity A x = (({i : ℕ | x ∈ A i}.encard : ℕ∞) : ℝ≥0∞) := by
  unfold fiberMultiplicity
  rw [← ENNReal.tsum_set_one {i : ℕ | x ∈ A i},
    tsum_subtype {i : ℕ | x ∈ A i} (fun _ : ℕ => (1 : ℝ≥0∞))]
  apply tsum_congr
  intro i
  by_cases hi : x ∈ A i <;> simp [hi]

theorem nth_count_other_of_encard_eq (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hcard : {i : ℕ | p i}.encard = {i : ℕ | q i}.encard) (i : ℕ) (hpi : p i) :
    q (Nat.nth q (Nat.count p i)) ∧ Nat.count q (Nat.nth q (Nat.count p i)) = Nat.count p i := by
  have henough : ∀ hq : {i : ℕ | q i}.Finite, Nat.count p i < hq.toFinset.card := by
    intro hq
    have hp : {i : ℕ | p i}.Finite := (Set.finite_iff_finite_of_encard_eq_encard hcard).mpr hq
    have hnat : hp.toFinset.card = hq.toFinset.card := by
      have h := hcard
      rw [hp.encard_eq_coe_toFinset_card, hq.encard_eq_coe_toFinset_card] at h
      exact_mod_cast h
    rw [← hnat]
    exact Nat.count_lt_card hp hpi
  exact ⟨Nat.nth_mem _ henough, Nat.count_nth henough⟩

def fiberNthMatch (A B : ℕ → Set X) (p : X × ℕ) : X × ℕ := by
  classical
  exact (p.1, Nat.nth (fun j => p.1 ∈ B j) (Nat.count (fun i => p.1 ∈ A i) p.2))

theorem fiberNthMatch_fst (A B : ℕ → Set X) (p : X × ℕ) : (fiberNthMatch A B p).1 = p.1 := rfl

theorem fiberNthMatch_measurable (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (fiberNthMatch A B) := by
  classical
  have hcount : Measurable (fun p : X × ℕ => Nat.count (fun i => p.1 ∈ A i) p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_nat_count (fun x j => x ∈ A j) hA i)
  have hnth : Measurable (fun p : X × ℕ => Nat.nth (fun i => p.1 ∈ B i) p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_nat_nth_total (fun x j => x ∈ B j) hB i)
  exact measurable_fst.prodMk (hnth.comp (measurable_fst.prodMk hcount))

theorem fiberNthMatch_mem (A B : ℕ → Set X) (x : X)
    (hcard : fiberMultiplicity A x = fiberMultiplicity B x) (i : ℕ) (hi : x ∈ A i) :
    fiberNthMatch A B (x,i) ∈ measureFiberSet B := by
  classical
  have hc : {j : ℕ | x ∈ A j}.encard = {j : ℕ | x ∈ B j}.encard := by
    rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard] at hcard
    exact ENat.toENNReal_inj.mp hcard
  exact (nth_count_other_of_encard_eq (fun j => x ∈ A j) (fun j => x ∈ B j) hc i hi).1

theorem fiberNthMatch_inverse (A B : ℕ → Set X) (x : X)
    (hcard : fiberMultiplicity A x = fiberMultiplicity B x) (i : ℕ) (hi : x ∈ A i) :
    fiberNthMatch B A (fiberNthMatch A B (x,i)) = (x,i) := by
  classical
  have hc : {j : ℕ | x ∈ A j}.encard = {j : ℕ | x ∈ B j}.encard := by
    rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard] at hcard
    exact ENat.toENNReal_inj.mp hcard
  have hmatch := nth_count_other_of_encard_eq (fun j => x ∈ A j) (fun j => x ∈ B j) hc i hi
  apply Prod.ext
  · rfl
  · change Nat.nth (fun j => x ∈ A j)
      (Nat.count (fun j => x ∈ B j) (Nat.nth (fun j => x ∈ B j) (Nat.count (fun j => x ∈ A j) i))) = i
    rw [hmatch.2]
    exact Nat.nth_count hi

def fiberActiveEquiv (A B : ℕ → Set X) (x : X)
    (hcard : fiberMultiplicity A x = fiberMultiplicity B x) :
    {i : ℕ | x ∈ A i} ≃ {j : ℕ | x ∈ B j} where
  toFun i := ⟨(fiberNthMatch A B (x,i)).2, fiberNthMatch_mem A B x hcard i i.property⟩
  invFun j := ⟨(fiberNthMatch B A (x,j)).2, fiberNthMatch_mem B A x hcard.symm j j.property⟩
  left_inv i := by
    apply Subtype.ext
    exact congrArg Prod.snd (fiberNthMatch_inverse A B x hcard i i.property)
  right_inv j := by
    apply Subtype.ext
    exact congrArg Prod.snd (fiberNthMatch_inverse B A x hcard.symm j j.property)

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberNthMatch_measurable
#print axioms MeasureUnitary.fiberNthMatch_inverse
