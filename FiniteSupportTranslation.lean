import ShiftGraph
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Algebra.Group.Torsion
import Mathlib.Data.Fintype.EquivFin

/-! Translation acts freely on nonempty finite subsets of a torsion-free
group. This is the stabilizer fact needed for the Walsh decomposition of
the free-group Bernoulli representation. -/

noncomputable section

namespace BenchmarkFiniteSupport

theorem translate_eq_self_implies_one
    {G : Type*} [Group G] [DecidableEq G] [IsMulTorsionFree G]
    (S : Finset G) (hS : S.Nonempty) (g : G)
    (htranslate : S.image (fun a => g * a) = S) : g = 1 := by
  classical
  obtain ⟨a, ha⟩ := hS
  have hstep : ∀ b ∈ S, g * b ∈ S := by
    intro b hb
    rw [← htranslate]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hmem : ∀ n : ℕ, g ^ n * a ∈ S := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih => simpa only [pow_succ', mul_assoc] using hstep (g ^ n * a) ih
  let f : ℕ → S := fun n => ⟨g ^ n * a, hmem n⟩
  have hninj : ¬ Function.Injective f := not_injective_infinite_finite f
  simp only [Function.Injective, not_forall, _root_.not_imp] at hninj
  obtain ⟨n, m, heq, hne⟩ := hninj
  have hp : g ^ n = g ^ m := mul_right_cancel (congrArg Subtype.val heq)
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have hz : g ^ (m - n) = 1 := by rw [pow_sub g hnm.le, ← hp, mul_inv_cancel]
    exact (pow_eq_one_iff_left (by omega : m - n ≠ 0)).mp hz
  · have hz : g ^ (n - m) = 1 := by rw [pow_sub g hmn.le, hp, mul_inv_cancel]
    exact (pow_eq_one_iff_left (by omega : n - m ≠ 0)).mp hz

theorem freeGroup_translate_eq_self_implies_one
    (S : Finset BenchmarkShift.Group) (hS : S.Nonempty) (g : BenchmarkShift.Group)
    (htranslate : S.image (fun a => g * a) = S) : g = 1 :=
  translate_eq_self_implies_one S hS g htranslate

end BenchmarkFiniteSupport

#print axioms BenchmarkFiniteSupport.freeGroup_translate_eq_self_implies_one
