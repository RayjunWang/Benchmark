import LpCountableAction

/-! Every finite-Lp class is meager in the actual product of real lines. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

def coordinateBound (a : RealSequences) (M : ℕ) : Set RealSequences :=
  {x | ∀ i, |x i - a i| ≤ M}

lemma isClosed_coordinateBound (a : RealSequences) (M : ℕ) :
    IsClosed (coordinateBound a M) := by
  unfold coordinateBound
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le (((continuous_apply i).sub continuous_const).abs) continuous_const

lemma interior_coordinateBound (a : RealSequences) (M : ℕ) :
    interior (coordinateBound a M) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp isOpen_interior x hx
  let k := I.sup id + 1
  have hkI : k ∉ I := by
    intro hk
    have h := Finset.le_sup (f := id) hk
    change I.sup id + 1 ≤ I.sup id at h
    omega
  let y := Function.update x k (a k + ((M : ℝ) + 1))
  have hy : y ∈ (I : Set ℕ).pi V := by
    intro i hi
    have hin : i ≠ k := by intro h; exact hkI (h ▸ hi)
    simpa only [y, Function.update_of_ne hin] using (hV i hi).2
  have hbad := interior_subset (hVI hy) k
  have heq : |y k - a k| = (M : ℝ) + 1 := by
    simp [y, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
  rw [heq] at hbad
  linarith

theorem lp_class_meagre (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : RealSequences) :
    IsMeagre {x | BenchmarkComparisons.LpDifference p.toReal a x} := by
  have hM (M : ℕ) : IsMeagre (coordinateBound a M) :=
    ((isClosed_coordinateBound a M).isNowhereDense_iff.mpr (interior_coordinateBound a M)).isMeagre
  apply (isMeagre_iUnion hM).mono
  intro x hx
  have hpos : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hmem : Memℓp (fun i => a i - x i) p :=
    (memℓp_gen_iff hpos).mpr (by simpa only [Real.norm_eq_abs] using hx)
  let v : Translations p := ⟨fun i => a i - x i, hmem⟩
  obtain ⟨M, hM⟩ := exists_nat_gt ‖v‖
  apply mem_iUnion.mpr
  refine ⟨M, fun i => ?_⟩
  have hb := lp.norm_apply_le_norm (p := p) (zero_lt_one.trans_le Fact.out).ne' v i
  have heq : ‖v i‖ = |x i - a i| := by simp only [v, Real.norm_eq_abs, abs_sub_comm]
  rw [heq] at hb
  exact hb.trans hM.le

end BenchmarkCountableReverse

#print axioms BenchmarkCountableReverse.lp_class_meagre
