import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-! An explicit product reduction for bounded null-sequence codes. The
boundedness hypothesis is essential: a naive weighted interleaving does
not preserve nullness for arbitrary unbounded arrays. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkBoundedNullProduct

def weight (i : ℕ) : ℝ := (1 / 2) ^ i

lemma weight_pos (i : ℕ) : 0 < weight i := by unfold weight; positivity
lemma weight_le_one (i : ℕ) : weight i ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

def code (x : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  weight (Nat.unpair j).1 * x (Nat.unpair j).1 (Nat.unpair j).2

lemma code_pair (x : ℕ → ℕ → ℝ) (i k : ℕ) :
    code x (Nat.pair i k) = weight i * x i k := by simp [code]

theorem continuous_code : Continuous code := by
  apply continuous_pi
  intro j
  exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _))

lemma pair_tendsto (i : ℕ) : Tendsto (Nat.pair i) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  exact eventually_atTop.2 ⟨N, fun k hk => hk.trans (Nat.right_le_pair _ _)⟩

theorem null_iff_rows (x y : ℕ → ℕ → ℝ)
    (hbounded : ∀ i k, |x i k - y i k| ≤ 1) :
    Tendsto (fun j => code x j - code y j) atTop (𝓝 0) ↔
      ∀ i, Tendsto (fun k => x i k - y i k) atTop (𝓝 0) := by
  classical
  constructor
  · intro h i
    have ht := h.comp (pair_tendsto i)
    have hd := ht.div_const (weight i)
    have hne : weight i ≠ 0 := (weight_pos i).ne'
    simpa only [Function.comp_def, code_pair, ← mul_sub, mul_div_cancel_left₀ _ hne,
      zero_div] using hd
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hw : Tendsto weight atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨I, hI⟩ := (Metric.tendsto_atTop.mp hw) ε hε
    have hex : ∀ i : Fin I, ∃ K, ∀ k ≥ K, |x i k - y i k| < ε := by
      intro i
      simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_atTop.mp (h i)) ε hε
    choose K hK using hex
    let s : Finset (ℕ × ℕ) := (Finset.univ : Finset (Fin I)).biUnion fun i =>
      (Finset.range (K i)).image (fun k => ((i : ℕ), k))
    let t : Finset ℕ := s.image (fun p => Nat.pair p.1 p.2)
    refine ⟨t.sup id + 1, fun j hj => ?_⟩
    let i := (Nat.unpair j).1
    let k := (Nat.unpair j).2
    have heq : code x j - code y j = weight i * (x i k - y i k) := by
      dsimp [code, i, k]
      ring
    rw [Real.dist_eq, sub_zero, heq, abs_mul, abs_of_pos (weight_pos i)]
    by_cases hi : i < I
    · have hk : K ⟨i, hi⟩ ≤ k := by
        by_contra hh
        have hs : (i, k) ∈ s := by
          apply Finset.mem_biUnion.mpr
          refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
        have ht : j ∈ t := by
          apply Finset.mem_image.mpr
          exact ⟨(i, k), hs, Nat.pair_unpair j⟩
        have hsup : j ≤ t.sup id := Finset.le_sup (f := id) ht
        omega
      have hsmall := hK ⟨i, hi⟩ k hk
      exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) (weight_le_one i)) hsmall
    · have hsmall := hI i (by omega)
      have hwε : weight i < ε := by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos (weight_pos i)] using hsmall
      calc
        weight i * |x i k - y i k| ≤ weight i :=
          mul_le_of_le_one_right (weight_pos i).le (hbounded i k)
        _ < ε := hwε

theorem exists_product_reduction {X : Type*} [MeasurableSpace X]
    (E : X → X → Prop) (F : X → ℕ → ℝ) (hF : Measurable F)
    (hbounded : ∀ x k, 0 ≤ F x k ∧ F x k ≤ 1)
    (hred : ∀ x y, E x y ↔ Tendsto (fun k => F x k - F y k) atTop (𝓝 0)) :
    ∃ G : (ℕ → X) → (ℕ → ℝ), Measurable G ∧
      (∀ x j, 0 ≤ G x j ∧ G x j ≤ 1) ∧
      ∀ x y, (∀ i, E (x i) (y i)) ↔
        Tendsto (fun j => G x j - G y j) atTop (𝓝 0) := by
  let G := fun x : ℕ → X => code (fun i => F (x i))
  have hrows : Measurable (fun x : ℕ → X => fun i => F (x i)) :=
    measurable_pi_lambda _ (fun i => hF.comp (measurable_pi_apply i))
  refine ⟨G, continuous_code.measurable.comp hrows, ?_, ?_⟩
  · intro x j
    change 0 ≤ weight _ * F (x _) _ ∧ weight _ * F (x _) _ ≤ 1
    exact ⟨mul_nonneg (weight_pos _).le (hbounded _ _).1,
      (mul_le_of_le_one_right (weight_pos _).le (hbounded _ _).2).trans (weight_le_one _)⟩
  · intro x y
    have hb : ∀ i k, |F (x i) k - F (y i) k| ≤ 1 := by
      intro i k
      exact abs_le.mpr ⟨by linarith [(hbounded (x i) k).1, (hbounded (y i) k).2],
        by linarith [(hbounded (x i) k).2, (hbounded (y i) k).1]⟩
    exact (forall_congr' fun i => hred (x i) (y i)).trans (null_iff_rows _ _ hb).symm

end BenchmarkBoundedNullProduct

#print axioms BenchmarkBoundedNullProduct.exists_product_reduction
