import CircleGrids
import Mathlib.Topology.Constructions

/-! Direct obstruction for the graph (coordinate inclusion, Hilbert feature).
This avoids adding the weighted character embedding to the Hilbert feature. -/

open Filter Topology Set
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceTail

open MeasureEquivalenceTorus MeasureEquivalenceGrid MeasureEquivalenceCircle

variable {H E : Type*} [NormedAddCommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma graph_long_bound (coord : H → ℕ → UnitAddCircle) (hzero : coord 0 = 0)
    (r : H → E) (hg : IsInducing (fun h => (coord h, r h))) :
    ∃ (N : ℕ) (c : ℝ), 0 < c ∧ ∀ h,
      (∀ k < N, coord h k = 0) → (1 / 4 : ℝ) ≤ ‖h‖ → c ≤ ‖r h - r 0‖ := by
  have hball : Metric.ball (0 : H) (1 / 4) ∈ 𝓝 (0 : H) :=
    Metric.ball_mem_nhds _ (by norm_num)
  rw [hg.nhds_eq_comap 0, Filter.mem_comap] at hball
  obtain ⟨s, hs, hsub⟩ := hball
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hs
  rw [hzero, nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  obtain ⟨c, hc, hcV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨I.sup id + 1, c, hc, fun h htail hnorm => ?_⟩
  by_contra! hsmall
  have hcoord : coord h ∈ U := htU (by
    intro k hk
    have hkbound : k ≤ I.sup id := Finset.le_sup (f := id) hk
    rw [htail k (by omega)]
    exact mem_of_mem_nhds (ht k))
  have hr : r h ∈ V := hcV (by simpa [Metric.mem_ball, dist_eq_norm] using hsmall)
  have hh : h ∈ Metric.ball (0 : H) (1 / 4) := hsub (hUV ⟨hcoord, hr⟩)
  have : ‖h‖ < (1 / 4 : ℝ) := by simpa [Metric.mem_ball] using hh
  linarith

theorem no_invariant_hilbert_graph
    (coord : H → ℕ → UnitAddCircle) (hzero : coord 0 = 0)
    (hgrids : ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ H),
      (∀ x k, k < N → coord (g x) k = 0) ∧
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ))
    (r : H → E) (hg : IsEmbedding (fun h => (coord h, r h)))
    (hinv : ∀ h k t, ‖r (h + t) - r (k + t)‖ = ‖r h - r k‖) : False := by
  obtain ⟨N, c, hc, hlong⟩ := graph_long_bound coord hzero r hg.isInducing
  have hr : Continuous r := continuous_snd.comp hg.continuous
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp
    (hr.continuousAt (x := 0)) (c / 3) (by positivity)
  obtain ⟨m, hm, g, htail, hglong, hgshort⟩ := hgrids N δ hδ
  letI : NeZero m := ⟨by omega⟩
  have hdisp (x y : Fin (m ^ 2) → ZMod m) :
      ‖r (g (x + y)) - r (g x)‖ = ‖r (g y) - r 0‖ := by
    rw [map_add, add_comm (g x) (g y)]
    simpa only [zero_add] using hinv (g y) 0 (g x)
  apply finite_grid_gap hm (r ∘ g) c hc
  · intro j x
    simpa only [Function.comp_apply, hdisp] using
      hlong _ (htail _) (hglong j)
  · intro ε x
    rw [Function.comp_apply, Function.comp_apply, hdisp]
    apply le_of_lt
    simpa only [dist_eq_norm] using hsmall
      (show dist (g (shortShift ε)) 0 < δ by simpa using hgshort ε)

variable (N : ℕ) {m n : ℕ}

/-- Insert N leading zero residues. -/
def pad : (Fin n → ZMod m) →+ (Fin (N + n) → ZMod m) where
  toFun x j := if hj : N ≤ j.val then x ⟨j.val - N, by omega⟩ else 0
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp only [Pi.add_apply]; split_ifs <;> simp

def padSigns (ε : Fin n → Fin 3) (j : Fin (N + n)) : Fin 3 :=
  if hj : N ≤ j.val then ε ⟨j.val - N, by omega⟩ else 1

lemma pad_short (ε : Fin n → Fin 3) :
    pad N (shortShift (m := m) ε) = shortShift (padSigns N ε) := by
  ext j
  simp only [pad, AddMonoidHom.coe_mk, ZeroHom.coe_mk, shortShift, padSigns]
  split_ifs <;> simp [step]

lemma pad_axis (j : Fin n) (a : ZMod m) :
    pad N (axisHom j a) = axisHom (⟨N + j.val, by omega⟩ : Fin (N + n)) a := by
  ext i
  simp only [pad, AddMonoidHom.coe_mk, ZeroHom.coe_mk, axisHom]
  by_cases hi : N ≤ i.val
  · rw [dif_pos hi]
    congr 1
    apply propext
    simp only [Fin.ext_iff]
    omega
  · rw [dif_neg hi]
    have hne : i ≠ (⟨N + j.val, by omega⟩ : Fin (N + n)) := by
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_mk] at this
      omega
    simp [hne]

variable (p : ℝ≥0∞) [NeZero m]

def tailGrid : (Fin n → ZMod m) →+ Hp p := (grid p).comp (pad N)

def tailGrid0 : (Fin n → ZMod m) →+ H0 := grid0.comp (pad N)

lemma tailGrid_zero (x : Fin n → ZMod m) {k : ℕ} (hk : k < N) :
    tailGrid N p x k = 0 := by
  simp [tailGrid, gridValue, pad, show k < N + n by omega, show ¬ N ≤ k by omega]

lemma tailGrid0_zero (x : Fin n → ZMod m) {k : ℕ} (hk : k < N) :
    ((tailGrid0 N x : H0) : Hp ⊤) k = 0 := tailGrid_zero N ⊤ x hk

lemma tailGrid_long (hp : p ≠ 0) (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖tailGrid N p (axisHom j ((m / 2 : ℕ) : ZMod m))‖ := by
  change (1 / 4 : ℝ) ≤ ‖grid p (pad N (axisHom j ((m / 2 : ℕ) : ZMod m)))‖
  rw [pad_axis]
  exact grid_long_bound p hp heven _

lemma tailGrid0_long (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖tailGrid0 N (axisHom j ((m / 2 : ℕ) : ZMod m))‖ :=
  tailGrid_long N ⊤ (by simp) heven j

lemma tailGrid_short_rpow (hp : 0 < p.toReal) (ε : Fin n → Fin 3) :
    ‖tailGrid (m := m) N p (shortShift ε)‖ ^ p.toReal ≤
      ((N + n : ℕ) : ℝ) * (1 / (m : ℝ)) ^ p.toReal := by
  change ‖grid p (pad N (shortShift ε))‖ ^ p.toReal ≤ _
  rw [pad_short]
  exact grid_short_rpow p hp _

lemma tailGrid0_short (ε : Fin n → Fin 3) :
    ‖tailGrid0 (m := m) N (shortShift ε)‖ ≤ 1 / (m : ℝ) := by
  change ‖grid0 (pad N (shortShift ε))‖ ≤ _
  rw [pad_short]
  exact grid0_short_bound _

lemma tailGrid_square_short_rpow (hp : 0 < p.toReal) (hm : 2 ≤ m) (hNm : N ≤ m)
    (ε : Fin (m ^ 2) → Fin 3) :
    ‖tailGrid (m := m) N p (shortShift ε)‖ ^ p.toReal ≤
      2 * (m : ℝ) ^ (2 - p.toReal) := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hNreal : (N : ℝ) ≤ m := by exact_mod_cast hNm
  have hsum : ((N + m ^ 2 : ℕ) : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have heq : (m : ℝ) ^ 2 * (1 / (m : ℝ)) ^ p.toReal =
      (m : ℝ) ^ (2 - p.toReal) := by
    rw [Real.rpow_sub (by linarith : (0 : ℝ) < m), Real.rpow_two]
    simp [one_div, Real.inv_rpow, div_eq_mul_inv]
  calc
    _ ≤ ((N + m ^ 2 : ℕ) : ℝ) * (1 / (m : ℝ)) ^ p.toReal :=
      tailGrid_short_rpow N p hp ε
    _ ≤ (2 * (m : ℝ) ^ 2) * (1 / (m : ℝ)) ^ p.toReal :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = 2 * (m : ℝ) ^ (2 - p.toReal) := by rw [mul_assoc, heq]

lemma exists_even_rpow_small_ge {r δ : ℝ} (hr : r < 0) (hδ : 0 < δ) :
    ∃ m : ℕ, 2 ≤ m ∧ N ≤ m ∧ Even m ∧ (m : ℝ) ^ r < δ := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨2 * (N + K + 1), by omega, by omega,
    ⟨N + K + 1, by omega⟩, hK _ (by omega)⟩

def hpCoordinates (x : Hp p) : ℕ → UnitAddCircle := x

def h0Coordinates (x : H0) : ℕ → UnitAddCircle := (x : Hp ⊤)

theorem H0_has_small_tail_grids :
    ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ H0),
      (∀ x k, k < N → h0Coordinates (g x) k = 0) ∧
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro N δ hδ
  obtain ⟨m, hm, _hNm, heven, hsmall⟩ :=
    exists_even_rpow_small_ge N (r := -1) (by norm_num) hδ
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, tailGrid0 N, fun x k hk => tailGrid0_zero N x hk,
    tailGrid0_long N heven, fun ε => ?_⟩
  apply (tailGrid0_short N ε).trans_lt
  simpa [Real.rpow_neg_one, one_div] using hsmall

theorem Hp_has_small_tail_grids [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ Hp p),
      (∀ x k, k < N → hpCoordinates p (g x) k = 0) ∧
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro N δ hδ
  have hp0 : 0 < p.toReal := by linarith
  have hpn : p ≠ 0 := by intro hz; norm_num [hz] at hp
  have hδp : 0 < δ ^ p.toReal := Real.rpow_pos_of_pos hδ p.toReal
  obtain ⟨m, hm, hNm, heven, hsmall⟩ :=
    exists_even_rpow_small_ge N (r := 2 - p.toReal) (δ := δ ^ p.toReal / 2)
      (by linarith) (by positivity)
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, tailGrid N p, fun x k hk => tailGrid_zero N p x hk,
    tailGrid_long N p hpn heven, fun ε => ?_⟩
  apply (Real.rpow_lt_rpow_iff (norm_nonneg _) hδ.le hp0).mp
  apply (tailGrid_square_short_rpow N p hp0 hm hNm ε).trans_lt
  linarith

/-- No embedding of the coordinate/density graph for actual H0, when only
the Hilbert feature distance is assumed invariant. -/
theorem no_H0_invariant_hilbert_graph (r : H0 → E)
    (hg : IsEmbedding (fun h => (h0Coordinates h, r h)))
    (hinv : ∀ h k t, ‖r (h + t) - r (k + t)‖ = ‖r h - r k‖) : False :=
  no_invariant_hilbert_graph h0Coordinates rfl H0_has_small_tail_grids r hg hinv

/-- The corresponding graph obstruction for actual Hp, finite p>2. The
ambient coordinate space carries its product topology. -/
theorem no_Hp_invariant_hilbert_graph [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (r : Hp p → E) (hg : IsEmbedding (fun h => (hpCoordinates p h, r h)))
    (hinv : ∀ h k t, ‖r (h + t) - r (k + t)‖ = ‖r h - r k‖) : False :=
  no_invariant_hilbert_graph (hpCoordinates p) rfl (Hp_has_small_tail_grids p hp) r hg hinv

end MeasureEquivalenceTail

#print axioms MeasureEquivalenceTail.graph_long_bound
#print axioms MeasureEquivalenceTail.no_invariant_hilbert_graph
#print axioms MeasureEquivalenceTail.tailGrid_short_rpow
#print axioms MeasureEquivalenceTail.no_H0_invariant_hilbert_graph
#print axioms MeasureEquivalenceTail.no_Hp_invariant_hilbert_graph
