import GridObstruction
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircle

open MeasureEquivalenceTorus MeasureEquivalenceGrid

abbrev Hp (p : ℝ≥0∞) := lp (fun _ : ℕ => UnitAddCircle) p

variable (p : ℝ≥0∞) {m n : ℕ} [NeZero m]

def gridValue (x : Fin n → ZMod m) (k : ℕ) : UnitAddCircle :=
  if hk : k < n then ZMod.toAddCircle (x ⟨k, hk⟩) else 0

def grid : (Fin n → ZMod m) →+ Hp p where
  toFun x := ⟨gridValue x, (memℓp_zero (by
    apply (Finset.finite_toSet (Finset.range n)).subset
    intro k hk
    by_contra hkn
    have : ¬ k < n := by simpa using hkn
    exact hk (by simp [gridValue, this]))).of_exponent_ge (by positivity)⟩
  map_zero' := by
    apply lp.ext
    funext k
    change gridValue (0 : Fin n → ZMod m) k = (0 : UnitAddCircle)
    simp [gridValue]
  map_add' x y := by
    ext k
    change gridValue (x + y) k = gridValue x k + gridValue y k
    simp only [gridValue]
    split_ifs <;> simp

@[simp] lemma grid_apply (x : Fin n → ZMod m) (k : ℕ) :
    grid p x k = gridValue x k := rfl

lemma grid_apply_fin (x : Fin n → ZMod m) (j : Fin n) :
    grid p x j = ZMod.toAddCircle (x j) := by simp [gridValue]

lemma grid_apply_ge (x : Fin n → ZMod m) {k : ℕ} (hk : n ≤ k) :
    grid p x k = 0 := by simp [gridValue, not_lt.mpr hk]

lemma circle_step_bound (t : Fin 3) :
    ‖ZMod.toAddCircle (step (m := m) t)‖ ≤ 1 / (m : ℝ) := by
  have hbase : ‖((1 / (m : ℝ) : ℝ) : UnitAddCircle)‖ ≤ 1 / (m : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
      using (QuotientAddGroup.norm_mk_le_norm
        (m := (1 / (m : ℝ) : ℝ)) (S := AddSubgroup.zmultiples (1 : ℝ)))
  have hone : ZMod.toAddCircle (1 : ZMod m) = ((1 / (m : ℝ) : ℝ) : UnitAddCircle) := by
    simpa using ZMod.toAddCircle_natCast (N := m) 1
  fin_cases t <;> simp [step, map_neg, hone] <;> simpa [one_div] using hbase

lemma half_turn_value (heven : Even m) :
    ZMod.toAddCircle ((m / 2 : ℕ) : ZMod m) = ((1 / 2 : ℝ) : UnitAddCircle) := by
  rw [ZMod.toAddCircle_natCast]
  congr 1
  have hmul : m / 2 * 2 = m := Nat.div_mul_cancel heven.two_dvd
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hreal : (m / 2 : ℕ) * (2 : ℝ) = m := by exact_mod_cast hmul
  apply (div_eq_iff hm).mpr
  linarith

lemma grid_long_bound (hp : p ≠ 0) (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖grid p (axisHom j ((m / 2 : ℕ) : ZMod m))‖ := by
  have h := lp.norm_apply_le_norm hp (grid p (axisHom j ((m / 2 : ℕ) : ZMod m))) j
  rw [grid_apply_fin] at h
  simp only [axisHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ite_true] at h
  rw [half_turn_value heven] at h
  have hnorm : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = (1 / 2 : ℝ) := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  rw [hnorm] at h
  exact (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num).trans h

lemma grid_short_coordinate (ε : Fin n → Fin 3) (k : ℕ) :
    ‖grid (m := m) p (shortShift ε) k‖ ≤ 1 / (m : ℝ) := by
  by_cases hk : k < n
  · simpa [gridValue, hk, shortShift] using circle_step_bound (m := m) (ε ⟨k, hk⟩)
  · simp [gridValue, hk]

lemma grid_short_sup (ε : Fin n → Fin 3) :
    ‖grid (m := m) ⊤ (shortShift ε)‖ ≤ 1 / (m : ℝ) :=
  lp.norm_le_of_forall_le (by positivity) (grid_short_coordinate ⊤ ε)

lemma grid_norm_rpow (hp : 0 < p.toReal) (x : Fin n → ZMod m) :
    ‖grid p x‖ ^ p.toReal = ∑ k ∈ Finset.range n, ‖grid p x k‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp]
  apply tsum_eq_sum
  intro k hk
  rw [grid_apply_ge p x (by simpa using hk), norm_zero, Real.zero_rpow hp.ne']

lemma grid_short_rpow (hp : 0 < p.toReal) (ε : Fin n → Fin 3) :
    ‖grid (m := m) p (shortShift ε)‖ ^ p.toReal ≤
      (n : ℝ) * (1 / (m : ℝ)) ^ p.toReal := by
  rw [grid_norm_rpow p hp]
  calc
    _ ≤ ∑ _k ∈ Finset.range n, (1 / (m : ℝ)) ^ p.toReal :=
      Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (norm_nonneg _)
        (grid_short_coordinate p ε k) hp.le
    _ = _ := by simp

lemma grid_square_short_rpow (hp : 0 < p.toReal) (ε : Fin (m ^ 2) → Fin 3) :
    ‖grid (m := m) p (shortShift ε)‖ ^ p.toReal ≤ (m : ℝ) ^ (2 - p.toReal) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  convert grid_short_rpow p hp ε using 1
  rw [Real.rpow_sub hm, Real.rpow_two]
  simp [Nat.cast_pow, one_div, Real.inv_rpow, div_eq_mul_inv]

/-- Even moduli can be chosen arbitrarily far out; the dimension is then m². -/
lemma exists_even_rpow_small {r δ : ℝ} (hr : r < 0) (hδ : 0 < δ) :
    ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ (m : ℝ) ^ r < δ := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ r < δ := ht.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨2 * (N + 1), by omega, ⟨N + 1, by omega⟩, hN _ (by omega)⟩

/-- The circle null-sequence group, with the inherited supremum norm. -/
def H0subgroup : AddSubgroup (Hp ⊤) where
  carrier := {x | Tendsto (fun k => x k) atTop (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds
  add_mem' hx hy := by simpa using hx.add hy
  neg_mem' hx := by simpa using hx.neg

abbrev H0 := H0subgroup

lemma grid_null (x : Fin n → ZMod m) : grid ⊤ x ∈ H0subgroup := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with k hk
  exact (grid_apply_ge ⊤ x hk).symm

def grid0 : (Fin n → ZMod m) →+ H0 :=
  (grid ⊤).codRestrict H0subgroup grid_null

lemma grid0_long_bound (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖grid0 (axisHom j ((m / 2 : ℕ) : ZMod m))‖ :=
  grid_long_bound ⊤ (by simp) heven j

lemma grid0_short_bound (ε : Fin n → Fin 3) :
    ‖grid0 (m := m) (shortShift ε)‖ ≤ 1 / (m : ℝ) := grid_short_sup ε

theorem H0_has_small_grids : ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
    (g : (Fin (m ^ 2) → ZMod m) →+ H0),
    (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
    (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro δ hδ
  obtain ⟨m, hm, heven, hsmall⟩ := exists_even_rpow_small (r := -1) (by norm_num) hδ
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, grid0, grid0_long_bound heven, fun ε => ?_⟩
  apply (grid0_short_bound ε).trans_lt
  simpa [Real.rpow_neg_one, one_div] using hsmall

theorem Hp_has_small_grids [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ Hp p),
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro δ hδ
  have hp0 : 0 < p.toReal := by linarith
  have hpn : p ≠ 0 := by intro hz; norm_num [hz] at hp
  obtain ⟨m, hm, heven, hsmall⟩ := exists_even_rpow_small
    (r := 2 - p.toReal) (by linarith) (Real.rpow_pos_of_pos hδ p.toReal)
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, grid p, grid_long_bound p hpn heven, fun ε => ?_⟩
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hδ.le hp0).mp
    ((grid_square_short_rpow p hp0 ε).trans_lt hsmall)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Concrete null-circle-sequence obstruction, with no grid assumptions. -/
theorem no_H0_invariant_hilbert_embedding (Ψ : H0 → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False :=
  no_invariant_hilbert_embedding H0_has_small_grids Ψ hΨ hinv

/-- Concrete finite-p circle-sequence obstruction. `2 < p.toReal` excludes
the infinite exponent, and `[Fact (1 ≤ p)]` supplies its standard lp metric. -/
theorem no_Hp_invariant_hilbert_embedding [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (Ψ : Hp p → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False :=
  no_invariant_hilbert_embedding (Hp_has_small_grids p hp) Ψ hΨ hinv

end MeasureEquivalenceCircle

#print axioms MeasureEquivalenceCircle.grid_long_bound
#print axioms MeasureEquivalenceCircle.grid_short_sup
#print axioms MeasureEquivalenceCircle.grid0_long_bound
#print axioms MeasureEquivalenceCircle.no_H0_invariant_hilbert_embedding
#print axioms MeasureEquivalenceCircle.no_Hp_invariant_hilbert_embedding
