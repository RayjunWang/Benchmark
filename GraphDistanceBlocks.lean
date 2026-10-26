import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The graph-distance block construction

This is the constructive part of Benchmark.tex, Theorem 3.1.  It proves an
actual Borel reduction to the usual null-difference relation, once the
finite refining separated Borel partitions and Borel bounded neighborhoods
have been supplied.  It does not claim to prove the Borel finite-coloring
theorem or instantiate those partitions on the full free-group shift.

The code uses a capped integer minimum, rather than extended real distance.
This makes the coordinates measurable from the Borel neighborhood sets.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkGraphBlocks

variable {X : Type*} (G : SimpleGraph X) (k : ℕ → ℕ)
  (color : ∀ n, X → Fin (k n))

def nearCell (n : ℕ) (i : Fin (k n)) (x : X) (r : ℕ) : Prop :=
  ∃ z, G.Reachable x z ∧ G.dist x z ≤ r ∧ color n z = i

lemma capped_exists (n : ℕ) (i : Fin (k n)) (x : X) :
    ∃ r, r = n + 1 ∨ nearCell G k color n i x r :=
  ⟨n + 1, Or.inl rfl⟩

def cappedDistance (n : ℕ) (i : Fin (k n)) (x : X) : ℕ :=
  by classical exact Nat.find (capped_exists G k color n i x)

lemma cappedDistance_le (n : ℕ) (i : Fin (k n)) (x : X) :
    cappedDistance G k color n i x ≤ n + 1 := by
  classical
  exact Nat.find_min' (capped_exists G k color n i x) (Or.inl rfl)

lemma cappedDistance_spec (n : ℕ) (i : Fin (k n)) (x : X) :
    cappedDistance G k color n i x = n + 1 ∨
      nearCell G k color n i x (cappedDistance G k color n i x) := by
  classical
  exact Nat.find_spec (capped_exists G k color n i x)

lemma cappedDistance_self (n : ℕ) (x : X) :
    cappedDistance G k color n (color n x) x = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  exact Or.inr ⟨x, SimpleGraph.Reachable.rfl, by simp, rfl⟩

lemma cappedDistance_le_add (n : ℕ) (i : Fin (k n))
    {x y : X} (hxy : G.Reachable x y) :
    cappedDistance G k color n i x ≤
      cappedDistance G k color n i y + G.dist x y := by
  classical
  rcases cappedDistance_spec G k color n i y with hcap | ⟨z, hyz, hdist, hcol⟩
  · calc
      cappedDistance G k color n i x ≤ n + 1 := cappedDistance_le G k color n i x
      _ ≤ cappedDistance G k color n i y + G.dist x y := by omega
  · apply Nat.find_min'
    refine Or.inr ⟨z, hxy.trans hyz, ?_, hcol⟩
    have ht := hxy.dist_triangle_left z
    omega

def coordinate (n : ℕ) (i : Fin (k n)) (x : X) : ℝ :=
  1 - (cappedDistance G k color n i x : ℝ) / ((n : ℝ) + 1)

lemma coordinate_nonneg (n : ℕ) (i : Fin (k n)) (x : X) :
    0 ≤ coordinate G k color n i x := by
  have hd : (cappedDistance G k color n i x : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast cappedDistance_le G k color n i x
  have hp : 0 < (n : ℝ) + 1 := by positivity
  unfold coordinate
  exact sub_nonneg.mpr ((div_le_one hp).mpr hd)

lemma coordinate_le_one (n : ℕ) (i : Fin (k n)) (x : X) :
    coordinate G k color n i x ≤ 1 := by
  unfold coordinate
  have : 0 ≤ (cappedDistance G k color n i x : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

lemma coordinate_self (n : ℕ) (x : X) :
    coordinate G k color n (color n x) x = 1 := by
  simp [coordinate, cappedDistance_self]

lemma coordinate_pos_witness (n : ℕ) (i : Fin (k n)) (x : X)
    (hp : 0 < coordinate G k color n i x) :
    ∃ z, G.Reachable x z ∧ G.dist x z ≤ n ∧ color n z = i := by
  rcases cappedDistance_spec G k color n i x with hcap | ⟨z, hxz, hd, hc⟩
  · have : coordinate G k color n i x = 0 := by
      simp [coordinate, hcap, Nat.cast_add, Nat.cast_one,
        ne_of_gt (by positivity : 0 < (n : ℝ) + 1)]
    linarith
  · refine ⟨z, hxz, ?_, hc⟩
    have hne : cappedDistance G k color n i x ≠ n + 1 := by
      intro hcap
      have : coordinate G k color n i x = 0 := by
        simp [coordinate, hcap, Nat.cast_add, Nat.cast_one,
          ne_of_gt (by positivity : 0 < (n : ℝ) + 1)]
      linarith
    have hb := cappedDistance_le G k color n i x
    omega

lemma coordinate_difference_le (n : ℕ) (i : Fin (k n))
    {x y : X} (hxy : G.Reachable x y) :
    |coordinate G k color n i x - coordinate G k color n i y| ≤
      (G.dist x y : ℝ) / ((n : ℝ) + 1) := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have h₁ : (cappedDistance G k color n i x : ℝ) ≤
      (cappedDistance G k color n i y : ℝ) + (G.dist x y : ℝ) := by
    exact_mod_cast cappedDistance_le_add G k color n i hxy
  have h₂ : (cappedDistance G k color n i y : ℝ) ≤
      (cappedDistance G k color n i x : ℝ) + (G.dist x y : ℝ) := by
    have h := cappedDistance_le_add G k color n i hxy.symm
    rw [SimpleGraph.dist_comm (G := G) (u := y) (v := x)] at h
    exact_mod_cast h
  have habs : |(cappedDistance G k color n i x : ℝ) -
      (cappedDistance G k color n i y : ℝ)| ≤ (G.dist x y : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold coordinate
  have heq : (1 - (cappedDistance G k color n i x : ℝ) / ((n : ℝ) + 1)) -
      (1 - (cappedDistance G k color n i y : ℝ) / ((n : ℝ) + 1)) =
      -((cappedDistance G k color n i x : ℝ) -
        (cappedDistance G k color n i y : ℝ)) / ((n : ℝ) + 1) := by ring
  rw [heq, abs_div, abs_neg, abs_of_pos hp]
  exact div_le_div_of_nonneg_right habs hp.le

def code (x : X) (j : ℕ) : ℝ :=
  if h : (Nat.unpair j).2 < k (Nat.unpair j).1 then
    coordinate G k color (Nat.unpair j).1 ⟨(Nat.unpair j).2, h⟩ x else 0

lemma code_pair (x : X) (n : ℕ) (i : Fin (k n)) :
    code G k color x (Nat.pair n i.val) = coordinate G k color n i x := by
  unfold code
  rw [Nat.unpair_pair]
  rw [dif_pos i.isLt]

lemma reachable_implies_null {x y : X} (hxy : G.Reachable x y) :
    Tendsto (fun j => code G k color x j - code G k color y j) atTop (𝓝 0) := by
  classical
  have hlim : Tendsto (fun n : ℕ => (G.dist x y : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using
      (tendsto_const_nhds (x := (G.dist x y : ℝ))).mul
        tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hlim ε hε
  let s : Finset (ℕ × ℕ) := (Finset.range N).biUnion fun n =>
    (Finset.range (k n)).image (fun i => (n, i))
  let t : Finset ℕ := s.image (fun p => Nat.pair p.1 p.2)
  refine ⟨t.sup id + 1, fun j hj => ?_⟩
  unfold code
  split_ifs with hi
  · have hn : N ≤ (Nat.unpair j).1 := by
      by_contra hh
      have hs : Nat.unpair j ∈ s := by
        apply Finset.mem_biUnion.mpr
        refine ⟨(Nat.unpair j).1, Finset.mem_range.mpr (by omega), ?_⟩
        exact Finset.mem_image.mpr
          ⟨(Nat.unpair j).2, Finset.mem_range.mpr hi, by simp⟩
      have ht : j ∈ t := Finset.mem_image.mpr ⟨Nat.unpair j, hs, Nat.pair_unpair j⟩
      have hsup : j ≤ t.sup id := Finset.le_sup (f := id) ht
      omega
    have hb := coordinate_difference_le G k color (Nat.unpair j).1
      ⟨(Nat.unpair j).2, hi⟩ hxy
    have hl := hN (Nat.unpair j).1 hn
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ (G.dist x y : ℝ) / ((Nat.unpair j).1 + 1))] at hl
    simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt hb hl
  · simpa using hε

/-- The inverse direction of the graph-distance construction. The separation
radius is `4(n+1)` to permit witnesses at integer distance at most `n`. -/
theorem null_iff_reachable
    (hrefine : ∀ n x y, color (n + 1) x = color (n + 1) y → color n x = color n y)
    (hseparate : ∀ x y, (∀ n, color n x = color n y) → x = y)
    (hfar : ∀ n x y, color n x = color n y → G.Reachable x y →
      G.dist x y ≤ 4 * (n + 1) → x = y)
    (x y : X) :
    Tendsto (fun j => code G k color x j - code G k color y j) atTop (𝓝 0) ↔
      G.Reachable x y := by
  classical
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) (1 / 4) (by norm_num)
    have hex : ∀ n, N ≤ n → ∃ z, G.Reachable y z ∧ G.dist y z ≤ n ∧
        color n z = color n x := by
      intro n hn
      have hc := hN (Nat.pair n (color n x).val)
        (le_trans hn (Nat.left_le_pair _ _))
      rw [code_pair, code_pair, coordinate_self, Real.dist_eq, sub_zero] at hc
      apply coordinate_pos_witness G k color n (color n x) y
      have hh := (abs_lt.mp hc).2
      linarith
    choose z hz using hex
    have hstep : ∀ n (hn : N ≤ n), z n hn = z (n + 1) (by omega) := by
      intro n hn
      apply hfar n
      · exact (hz n hn).2.2.trans
          (hrefine n _ _ (hz (n + 1) (by omega)).2.2).symm
      · exact (hz n hn).1.symm.trans (hz (n + 1) (by omega)).1
      · have ht := ((hz n hn).1.symm).dist_triangle_left (z (n + 1) (by omega))
        rw [SimpleGraph.dist_comm (G := G) (u := z n hn) (v := y)] at ht
        have ha := (hz n hn).2.1
        have hb := (hz (n + 1) (by omega)).2.1
        omega
    have hconst : ∀ n (hn : N ≤ n), z n hn = z N le_rfl := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih => exact (hstep n hn).symm.trans ih
    have hback : ∀ a b, a ≤ b → ∀ u v,
        color b u = color b v → color a u = color a v := by
      intro a b hab u v hc
      induction b, hab using Nat.le_induction with
      | base => exact hc
      | succ b hab ih => exact ih (hrefine b u v hc)
    have heq : z N le_rfl = x := by
      apply hseparate
      intro n
      have hn : N ≤ max N n := le_max_left _ _
      have hc := (hz (max N n) hn).2.2
      rw [hconst (max N n) hn] at hc
      exact hback n (max N n) (le_max_right _ _) _ _ hc
    exact ((hz N le_rfl).1.trans (heq ▸ SimpleGraph.Reachable.rfl)).symm
  · exact reachable_implies_null G k color

variable [MeasurableSpace X]

theorem measurable_coordinate
    (hnear : ∀ n (i : Fin (k n)) r, MeasurableSet {x | nearCell G k color n i x r})
    (n : ℕ) (i : Fin (k n)) : Measurable (coordinate G k color n i) := by
  classical
  have hd : Measurable (cappedDistance G k color n i) := by
    apply measurable_find
    intro r
    by_cases hr : r = n + 1
    · simp only [hr, true_or, setOf_true]
      exact MeasurableSet.univ
    · simpa only [hr, false_or] using hnear n i r
  have hc : Measurable (fun x => (cappedDistance G k color n i x : ℝ)) :=
    (measurable_from_nat : Measurable (fun a : ℕ => (a : ℝ))).comp hd
  exact measurable_const.sub (hc.div_const _)

theorem measurable_code
    (hnear : ∀ n (i : Fin (k n)) r, MeasurableSet {x | nearCell G k color n i x r}) :
    Measurable (code G k color) := by
  classical
  apply measurable_pi_lambda
  intro j
  unfold code
  split_ifs
  · exact measurable_coordinate G k color hnear _ _
  · exact measurable_const

theorem exists_borel_null_reduction
    (hrefine : ∀ n x y, color (n + 1) x = color (n + 1) y → color n x = color n y)
    (hseparate : ∀ x y, (∀ n, color n x = color n y) → x = y)
    (hfar : ∀ n x y, color n x = color n y → G.Reachable x y →
      G.dist x y ≤ 4 * (n + 1) → x = y)
    (hnear : ∀ n (i : Fin (k n)) r, MeasurableSet {x | nearCell G k color n i x r}) :
    ∃ F : X → (ℕ → ℝ), Measurable F ∧
      (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, G.Reachable x y ↔
        Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  classical
  refine ⟨code G k color, measurable_code G k color hnear, ?_, ?_⟩
  · intro x j
    unfold code
    split_ifs
    · exact ⟨coordinate_nonneg G k color _ _ _, coordinate_le_one G k color _ _ _⟩
    · norm_num
  · intro x y
    exact (null_iff_reachable G k color hrefine hseparate hfar x y).symm

end BenchmarkGraphBlocks

#print axioms BenchmarkGraphBlocks.exists_borel_null_reduction
