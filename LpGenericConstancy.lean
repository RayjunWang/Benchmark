import LpPrefixInterpolation
import LpCountableLocal

/-! Finite-prefix interpolation propagates exact local-orbit equality to
generic constancy on a product-open set. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

def fraction (m : ℕ) (j : Fin (m + 1)) : ℝ := (j : ℝ) / m

lemma fraction_nonneg (m : ℕ) (j : Fin (m + 1)) : 0 ≤ fraction m j := by
  unfold fraction
  positivity

lemma fraction_le_one (m : ℕ) (j : Fin (m + 1)) : fraction m j ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    simp [fraction]
  · unfold fraction
    apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hm)).mpr
    exact_mod_cast Nat.le_of_lt_succ j.isLt

lemma fraction_step (m : ℕ) (hm : 0 < m) (j : Fin m) :
    fraction m j.succ - fraction m j.castSucc = 1 / (m : ℝ) := by
  unfold fraction
  simp only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

lemma fraction_last (m : ℕ) (hm : 0 < m) : fraction m (Fin.last m) = 1 := by
  simp [fraction, (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]

theorem prefix_interpolation_generic_pairs (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set RealSequences) (hCo : IsOpen C) (hC : PrefixConvex C)
    (D : Set RealSequences) (hD : D ∈ residual RealSequences)
    (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ C, ∀ k : Translations p, ‖k‖ < ε →
      y ∈ D → y + coordinates p k ∈ D → f y = f (y + coordinates p k)) :
    ∀ᶠ z : C × C in residual (C × C), f z.1 = f z.2 := by
  classical
  let P (N m : ℕ) (j : Fin (m + 1)) : C × C → C :=
    prefixMixOn C hC N (fraction m j) (fraction_nonneg m j) (fraction_le_one m j)
  have hDC : ∀ᶠ x : C in residual C, (x : RealSequences) ∈ D :=
    BenchmarkJump.eventually_residual_open_subspace C hCo hD
  have hAll : ∀ᶠ z : C × C in residual (C × C),
      ∀ N m : ℕ, ∀ j : Fin (m + 1), (P N m j z : RealSequences) ∈ D := by
    apply eventually_countable_forall.mpr
    intro N
    apply eventually_countable_forall.mpr
    intro m
    apply eventually_countable_forall.mpr
    intro j
    exact tendsto_residual_of_isOpenMap (continuous_prefixMixOn C hC N _ _ _)
      (isOpenMap_prefixMixOn C hCo hC N _ _ _) hDC
  have hD1 : ∀ᶠ z : C × C in residual (C × C), (z.1 : RealSequences) ∈ D :=
    tendsto_residual_of_isOpenMap continuous_fst isOpenMap_fst hDC
  have hD2 : ∀ᶠ z : C × C in residual (C × C), (z.2 : RealSequences) ∈ D :=
    tendsto_residual_of_isOpenMap continuous_snd isOpenMap_snd hDC
  filter_upwards [hAll, hD1, hD2] with z hz hz1 hz2
  have hChain (N : ℕ) : f z.1 = f (prefixMix N 1 (z.1, z.2)) := by
    let v := prefixVector p N ((z.2 : RealSequences) - (z.1 : RealSequences))
    obtain ⟨m, hm⟩ := exists_nat_gt (‖v‖ / ε)
    have hmpos : 0 < m := by
      have hmreal : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hε.le) hm
      exact_mod_cast hmreal
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hvdiv : ‖v‖ / (m : ℝ) < ε := by
      apply (div_lt_iff₀ hmreal).mpr
      have hv := (div_lt_iff₀ hε).mp hm
      linarith
    have hStep (j : Fin m) : f (P N m j.castSucc z) = f (P N m j.succ z) := by
      let k : Translations p :=
        (fraction m j.succ - fraction m j.castSucc) • v
      have hk : ‖k‖ < ε := by
        dsimp only [k]
        rw [norm_smul, Real.norm_eq_abs, fraction_step m hmpos j,
          abs_of_pos (div_pos zero_lt_one hmreal)]
        simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using hvdiv
      have heq : (P N m j.succ z : RealSequences) =
          (P N m j.castSucc z : RealSequences) + coordinates p k :=
        prefixMix_add_vector p N _ _ z.1 z.2
      have h := hSmall (P N m j.castSucc z) (P N m j.castSucc z).property
        k hk (hz N m j.castSucc) (by rw [← heq]; exact hz N m j.succ)
      rwa [← heq] at h
    have hAux : ∀ j : ℕ, ∀ hj : j ≤ m,
        f (P N m 0 z) = f (P N m ⟨j, Nat.lt_succ_of_le hj⟩ z) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
          intro hj
          have hjm : j < m := by omega
          exact (ih (by omega)).trans (hStep ⟨j, hjm⟩)
    have he := hAux m le_rfl
    have hstart : (P N m 0 z : RealSequences) = z.1 := by
      change prefixMix N (fraction m 0) (z.1, z.2) = _
      simp only [fraction, Fin.val_zero, Nat.cast_zero, zero_div]
      exact prefixMix_zero N z.1 z.2
    have hend : (P N m (Fin.last m) z : RealSequences) = prefixMix N 1 (z.1, z.2) := by
      change prefixMix N (fraction m (Fin.last m)) (z.1, z.2) = _
      rw [fraction_last m hmpos]
    change f (P N m 0 z) = f (P N m (Fin.last m) z) at he
    rwa [hstart, hend] at he
  have hMixD (N : ℕ) : prefixMix N 1 ((z.1 : RealSequences), z.2) ∈ D := by
    simpa only [P, prefixMixOn, fraction_last 1 (by norm_num)] using hz N 1 (Fin.last 1)
  let S : Set (RealSequences × RealSequences) := {q | q ∈ D ×ˢ D ∧ f q.1 = f q.2}
  apply equality_of_mem_closure D f hf S (fun q hq => hq.1) (fun q hq => hq.2)
    ((z.1 : RealSequences), z.2) ⟨hz1, hz2⟩
  apply mem_closure_of_tendsto
    (tendsto_const_nhds.prodMk_nhds (tendsto_prefixMix_one z.1 z.2))
  exact Eventually.of_forall fun N => ⟨⟨hz1, hMixD N⟩, hChain N⟩

theorem prefix_interpolation_generic_constant (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set RealSequences) (hCo : IsOpen C) (hCn : C.Nonempty) (hC : PrefixConvex C)
    (D : Set RealSequences) (hD : D ∈ residual RealSequences)
    (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ C, ∀ k : Translations p, ‖k‖ < ε →
      y ∈ D → y + coordinates p k ∈ D → f y = f (y + coordinates p k)) :
    ∃ a : BenchmarkShift.Point, ∀ᶠ x : C in residual C, f x = a := by
  letI : Nonempty C := hCn.to_subtype
  letI : BaireSpace C := hCo.baireSpace
  obtain ⟨x, hx⟩ := BenchmarkJump.exists_residual_section
    (prefix_interpolation_generic_pairs p C hCo hC D hD f hf ε hε hSmall)
  exact ⟨f x, hx.mono fun y hy => hy.symm⟩

end BenchmarkCountableReverse

#print axioms BenchmarkCountableReverse.prefix_interpolation_generic_constant
