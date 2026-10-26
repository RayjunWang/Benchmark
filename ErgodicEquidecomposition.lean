import NonsingularDichotomy
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Greedy measurable equidecomposition for finite equal-mass sets under
an actual ergodic, measure-preserving action of a countable group. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceEquidecomposition

open MeasureEquivalenceRigidity

variable {G Z : Type*} [Group G] [MulAction G Z]

/-- If no translate of one measurable set meets the other, ergodicity
forces one of the two sets to be null, even for an infinite measure. -/
theorem one_null_of_no_translated_overlap [Countable G] [MeasurableSpace Z]
    [MeasurableConstSMul G Z] (μ : Measure Z)
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hB : MeasurableSet B)
    (hdisj : ∀ g : G, Disjoint A ((fun z : Z => g • z) ⁻¹' B)) :
    μ A = 0 ∨ μ B = 0 := by
  have hm : MeasurableSet (orbitSaturation (G := G) B) :=
    MeasurableSet.iUnion (fun g => hB.preimage (measurable_const_smul g))
  rcases herg _ hm (preimage_orbitSaturation B) with hzero | hconull
  · exact Or.inr (measure_mono_null (subset_orbitSaturation B) hzero)
  · left
    apply measure_mono_null _ hconull
    intro z hz hsat
    obtain ⟨g, hg⟩ := mem_iUnion.mp hsat
    exact Set.disjoint_left.mp (hdisj g) hz hg

/-- One stage keeps precisely the unmatched source and target points. -/
def greedyStep (e : ℕ → G) (n : ℕ) (p : Set Z × Set Z) : Set Z × Set Z :=
  let C := p.1 ∩ (fun z : Z => e n • z) ⁻¹' p.2
  (p.1 \ C, p.2 \ ((fun z : Z => (e n)⁻¹ • z) ⁻¹' C))

def greedyRemainder (e : ℕ → G) (A B : Set Z) : ℕ → Set Z × Set Z
  | 0 => (A, B)
  | n+1 => greedyStep e n (greedyRemainder e A B n)

def greedyPiece (e : ℕ → G) (A B : Set Z) (n : ℕ) : Set Z :=
  (greedyRemainder e A B n).1 ∩
    (fun z : Z => e n • z) ⁻¹' (greedyRemainder e A B n).2

def greedyTarget (e : ℕ → G) (A B : Set Z) (n : ℕ) : Set Z :=
  (fun z : Z => (e n)⁻¹ • z) ⁻¹' greedyPiece e A B n

theorem greedy_source_succ (e : ℕ → G) (A B : Set Z) (n : ℕ) :
    (greedyRemainder e A B (n+1)).1 =
      (greedyRemainder e A B n).1 \ greedyPiece e A B n := rfl

theorem greedy_target_succ (e : ℕ → G) (A B : Set Z) (n : ℕ) :
    (greedyRemainder e A B (n+1)).2 =
      (greedyRemainder e A B n).2 \ greedyTarget e A B n := rfl

theorem greedy_measurable [MeasurableSpace Z] [MeasurableConstSMul G Z]
    (e : ℕ → G) (A B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∀ n, MeasurableSet (greedyRemainder e A B n).1 ∧
      MeasurableSet (greedyRemainder e A B n).2 := by
  intro n
  induction n with
  | zero => exact ⟨hA, hB⟩
  | succ n ih =>
    have hC : MeasurableSet (greedyPiece e A B n) :=
      ih.1.inter (ih.2.preimage (measurable_const_smul _))
    exact ⟨ih.1.diff hC, ih.2.diff (hC.preimage (measurable_const_smul _))⟩

theorem greedy_source_antitone (e : ℕ → G) (A B : Set Z) :
    Antitone (fun n => (greedyRemainder e A B n).1) := by
  apply antitone_nat_of_succ_le
  intro n
  exact Set.diff_subset

theorem greedy_target_antitone (e : ℕ → G) (A B : Set Z) :
    Antitone (fun n => (greedyRemainder e A B n).2) := by
  apply antitone_nat_of_succ_le
  intro n
  exact Set.diff_subset

theorem greedyTarget_subset (e : ℕ → G) (A B : Set Z) (n : ℕ) :
    greedyTarget e A B n ⊆ (greedyRemainder e A B n).2 := by
  intro z hz
  have h : e n • ((e n)⁻¹ • z) ∈ (greedyRemainder e A B n).2 := hz.2
  simpa only [smul_inv_smul] using h

theorem greedy_final_disjoint (e : ℕ → G) (he : Function.Surjective e)
    (A B : Set Z) (g : G) :
    Disjoint (⋂ n, (greedyRemainder e A B n).1)
      ((fun z : Z => g • z) ⁻¹' (⋂ n, (greedyRemainder e A B n).2)) := by
  obtain ⟨n, rfl⟩ := he g
  apply Set.disjoint_left.mpr
  intro z hz ht
  have hzn := mem_iInter.mp hz n
  have htn := mem_iInter.mp ht n
  have hnext := mem_iInter.mp hz (n+1)
  exact hnext.2 ⟨hzn, htn⟩

theorem final_remainder_eq_diff_iUnion (R C : ℕ → Set Z) (A : Set Z)
    (h0 : R 0 = A) (hstep : ∀ n, R (n+1) = R n \ C n) :
    (⋂ n, R n) = A \ ⋃ n, C n := by
  ext z
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · simpa only [← h0] using mem_iInter.mp hz 0
    · intro hC
      obtain ⟨n, hn⟩ := mem_iUnion.mp hC
      have hnext := mem_iInter.mp hz (n+1)
      rw [hstep] at hnext
      exact hnext.2 hn
  · rintro ⟨hzA, hzC⟩
    apply mem_iInter.mpr
    intro n
    induction n with
    | zero => simpa only [h0] using hzA
    | succ n ih =>
      rw [hstep]
      exact ⟨ih, fun hz => hzC (mem_iUnion.mpr ⟨n, hz⟩)⟩

theorem removed_pieces_pairwise_disjoint (R C : ℕ → Set Z)
    (hanti : Antitone R) (hC : ∀ n, C n ⊆ R n)
    (hstep : ∀ n, R (n+1) = R n \ C n) :
    Pairwise (fun i j => Disjoint (C i) (C j)) := by
  have hlt (i j : ℕ) (hij : i < j) : Disjoint (C i) (C j) := by
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hznext := hanti (Nat.succ_le_of_lt hij) (hC j hzj)
    rw [hstep] at hznext
    exact hznext.2 hzi
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

section Measure

variable [MeasurableSpace Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp

theorem greedy_target_mass (e : ℕ → G) (A B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    μ (greedyTarget e A B n) = μ (greedyPiece e A B n) := by
  apply (hmp ((e n)⁻¹)).measure_preimage
  exact ((greedy_measurable e A B hA hB n).1.inter
    ((greedy_measurable e A B hA hB n).2.preimage (measurable_const_smul _))).nullMeasurableSet

theorem greedy_equal_remainder_mass (e : ℕ → G) (A B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∀ n, μ (greedyRemainder e A B n).1 = μ (greedyRemainder e A B n).2 := by
  intro n
  induction n with
  | zero => exact hmass
  | succ n ih =>
    have hm := greedy_measurable e A B hA hB n
    have hCsub : greedyPiece e A B n ⊆ (greedyRemainder e A B n).1 := inter_subset_left
    have hCm : MeasurableSet (greedyPiece e A B n) :=
      hm.1.inter (hm.2.preimage (measurable_const_smul _))
    have hCf : μ (greedyPiece e A B n) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (hCsub.trans (greedy_source_antitone e A B (Nat.zero_le n))))
    have hTC := greedy_target_mass μ hmp e A B hA hB n
    rw [greedy_source_succ, greedy_target_succ,
      measure_diff hCsub hCm.nullMeasurableSet hCf,
      measure_diff (greedyTarget_subset e A B n)
        (hCm.preimage (measurable_const_smul _)).nullMeasurableSet (hTC.trans_ne hCf),
      hTC, ih]

theorem greedy_final_equal_mass (e : ℕ → G) (A B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    μ (⋂ n, (greedyRemainder e A B n).1) =
      μ (⋂ n, (greedyRemainder e A B n).2) := by
  rw [(greedy_source_antitone e A B).measure_iInter
      (fun n => (greedy_measurable e A B hA hB n).1.nullMeasurableSet) ⟨0, hfin⟩,
    (greedy_target_antitone e A B).measure_iInter
      (fun n => (greedy_measurable e A B hA hB n).2.nullMeasurableSet)
      ⟨0, hmass.symm.trans_ne hfin⟩]
  simp_rw [greedy_equal_remainder_mass μ hmp e A B hA hB hfin hmass]

theorem greedy_final_null [Countable G]
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (e : ℕ → G) (he : Function.Surjective e) (A B : Set Z)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    μ (A \ ⋃ n, greedyPiece e A B n) = 0 ∧
      μ (B \ ⋃ n, greedyTarget e A B n) = 0 := by
  have hleft := final_remainder_eq_diff_iUnion
    (fun n => (greedyRemainder e A B n).1) (greedyPiece e A B) A rfl
    (greedy_source_succ e A B)
  have hright := final_remainder_eq_diff_iUnion
    (fun n => (greedyRemainder e A B n).2) (greedyTarget e A B) B rfl
    (greedy_target_succ e A B)
  rw [← hleft, ← hright]
  have heq := greedy_final_equal_mass μ hmp e A B hA hB hfin hmass
  have hnull := one_null_of_no_translated_overlap μ herg
    (⋂ n, (greedyRemainder e A B n).1) (⋂ n, (greedyRemainder e A B n).2)
    (MeasurableSet.iInter (fun n => (greedy_measurable e A B hA hB n).2))
    (greedy_final_disjoint e he A B)
  rcases hnull with h | h
  · exact ⟨h, heq ▸ h⟩
  · exact ⟨heq.symm ▸ h, h⟩

/-- Every pair of measurable equal finite-mass sets admits an actual
countable measurable equidecomposition modulo null sets. Both families
are pairwise disjoint; the pieces translate to the corresponding targets. -/
theorem exists_equidecomposition [Countable G]
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ (e : ℕ → G) (C T : ℕ → Set Z),
      (∀ n, MeasurableSet (C n) ∧ MeasurableSet (T n)) ∧
      (∀ n, C n ⊆ A ∧ T n ⊆ B) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      (∀ n, T n = (fun z : Z => (e n)⁻¹ • z) ⁻¹' C n) ∧
      μ (A \ ⋃ n, C n) = 0 ∧ μ (B \ ⋃ n, T n) = 0 := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  refine ⟨e, greedyPiece e A B, greedyTarget e A B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hm := greedy_measurable e A B hA hB n
    have hC : MeasurableSet (greedyPiece e A B n) :=
      hm.1.inter (hm.2.preimage (measurable_const_smul _))
    exact ⟨hC, hC.preimage (measurable_const_smul _)⟩
  · intro n
    exact ⟨inter_subset_left.trans (greedy_source_antitone e A B (Nat.zero_le n)),
      (greedyTarget_subset e A B n).trans (greedy_target_antitone e A B (Nat.zero_le n))⟩
  · exact removed_pieces_pairwise_disjoint _ _ (greedy_source_antitone e A B)
      (fun _ => inter_subset_left) (greedy_source_succ e A B)
  · exact removed_pieces_pairwise_disjoint _ _ (greedy_target_antitone e A B)
      (greedyTarget_subset e A B) (greedy_target_succ e A B)
  · exact fun _ => rfl
  · exact greedy_final_null μ hmp herg e he A B hA hB hfin hmass

end Measure

end MeasureEquivalenceEquidecomposition

#print axioms MeasureEquivalenceEquidecomposition.one_null_of_no_translated_overlap
#print axioms MeasureEquivalenceEquidecomposition.greedy_final_disjoint
#print axioms MeasureEquivalenceEquidecomposition.exists_equidecomposition
