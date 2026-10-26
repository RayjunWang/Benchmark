import FiniteTorus
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Topology.Maps.Basic

/-! The dimension-uniform contradiction, including the two continuity
quantifiers. Actual circle-sequence grids are instantiated in a separate file. -/

open Filter Topology
open scoped Topology BigOperators

namespace MeasureEquivalenceGrid

open MeasureEquivalenceTorus

variable {H E : Type*} [NormedAddCommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inverse continuity at the identity provides one bound for all long steps. -/
lemma inducing_long_bound (Ψ : H → E) (hΨ : IsInducing Ψ) :
    ∃ c > 0, ∀ h : H, (1 / 4 : ℝ) ≤ ‖h‖ → c ≤ ‖Ψ h - Ψ 0‖ := by
  have hball : Metric.ball (0 : H) (1 / 4) ∈ 𝓝 (0 : H) :=
    Metric.ball_mem_nhds _ (by norm_num)
  rw [hΨ.nhds_eq_comap 0, Filter.mem_comap] at hball
  obtain ⟨s, hs, hsub⟩ := hball
  obtain ⟨c, hc, hcs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨c, hc, fun h hh => ?_⟩
  by_contra! hcontra
  have hm : h ∈ Metric.ball (0 : H) (1 / 4) :=
    hsub (hcs (by simpa [Metric.mem_ball, dist_eq_norm] using hcontra))
  have : ‖h‖ < (1 / 4 : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hm
  linarith

/-- One finite torus is already contradictory when the long steps all have
length at least c and all the short steps have length at most c/3. -/
theorem finite_grid_gap {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (F : (Fin (m ^ 2) → ZMod m) → E) (c : ℝ) (hc : 0 < c)
    (hlong : ∀ j x, c ≤
      ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖)
    (hshort : ∀ ε x,
      ‖F (x + shortShift ε) - F x‖ ≤ c / 3) : False := by
  classical
  have hlow : (m : ℝ) ^ 2 * c ^ 2 ≤
      ∑ j : Fin (m ^ 2), 𝔼 x,
        ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖ ^ 2 := by
    calc
      (m : ℝ) ^ 2 * c ^ 2 = ∑ _j : Fin (m ^ 2), 𝔼 _x : Fin (m ^ 2) → ZMod m,
          c ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.expect_le_expect fun x _ => by
        exact pow_le_pow_left₀ hc.le (hlong j x) 2
  have hupp : (𝔼 ε : Fin (m ^ 2) → Fin 3, 𝔼 x,
      ‖F (x + shortShift ε) - F x‖ ^ 2) ≤ (c / 3) ^ 2 := by
    calc
      _ ≤ (𝔼 _ε : Fin (m ^ 2) → Fin 3, 𝔼 _x : Fin (m ^ 2) → ZMod m,
          (c / 3) ^ 2) :=
        Finset.expect_le_expect fun ε _ => Finset.expect_le_expect fun x _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hshort ε x) 2
      _ = _ := by simp
  have htor := half_turn_real_hilbert F hm (by simp)
  have hbound : (m : ℝ) ^ 2 * c ^ 2 ≤ 4 * (m : ℝ) ^ 2 * (c / 3) ^ 2 :=
    hlow.trans (htor.trans (mul_le_mul_of_nonneg_left hupp (by positivity)))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : 0 < (m : ℝ) ^ 2 * c ^ 2 := by positivity
  nlinarith

/-- An abstract grid criterion with the complete order of quantifiers.
The grid, modulus and dimension may depend on delta; the continuity constants
and long-step lower bound cannot depend on them. -/
theorem no_invariant_hilbert_embedding
    (hgrids : ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
      (grid : (Fin (m ^ 2) → ZMod m) →+ H),
      (∀ j, (1 / 4 : ℝ) ≤ ‖grid (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖grid (shortShift ε)‖ < δ))
    (Ψ : H → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False := by
  obtain ⟨c, hc, hlong⟩ := inducing_long_bound Ψ hΨ.isInducing
  obtain ⟨δ, hδ, hsmall⟩ :=
    Metric.continuousAt_iff.mp (hΨ.continuous.continuousAt (x := 0)) (c / 3)
      (by positivity)
  obtain ⟨m, hm, grid, hgridlong, hgridshort⟩ := hgrids δ hδ
  letI : NeZero m := ⟨by omega⟩
  have hdisp (x y : Fin (m ^ 2) → ZMod m) :
      ‖Ψ (grid (x + y)) - Ψ (grid x)‖ = ‖Ψ (grid y) - Ψ 0‖ := by
    rw [map_add, add_comm (grid x) (grid y)]
    simpa only [zero_add] using hinv (grid y) 0 (grid x)
  apply finite_grid_gap hm (Ψ ∘ grid) c hc
  · intro j x
    simpa only [Function.comp_apply, hdisp] using hlong _ (hgridlong j)
  · intro ε x
    rw [Function.comp_apply, Function.comp_apply, hdisp]
    apply le_of_lt
    simpa only [dist_eq_norm] using hsmall
      (show dist (grid (shortShift ε)) 0 < δ by simpa using hgridshort ε)

end MeasureEquivalenceGrid

#print axioms MeasureEquivalenceGrid.inducing_long_bound
#print axioms MeasureEquivalenceGrid.finite_grid_gap
#print axioms MeasureEquivalenceGrid.no_invariant_hilbert_embedding
