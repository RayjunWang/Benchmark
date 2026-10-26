import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Logic.Equiv.Fin.Basic

open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleReduction

/-!
The domain and codomain sequence spaces below have their product topologies.
The lp relations are actual summability predicates, and the null relations
are actual convergence-to-zero predicates. All chord estimates and the
even/odd real interleaving are proved, rather than supplied as hypotheses.
-/

def circleEmbed (t : UnitAddCircle) : ℂ := AddCircle.toCircle t

lemma continuous_circleEmbed : Continuous circleEmbed :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

@[simp] lemma circleEmbed_re_mk (r : ℝ) :
    (circleEmbed (r : UnitAddCircle)).re = Real.cos (2 * Real.pi * r) := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re]

@[simp] lemma circleEmbed_im_mk (r : ℝ) :
    (circleEmbed (r : UnitAddCircle)).im = Real.sin (2 * Real.pi * r) := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im]

lemma circle_rep (t : UnitAddCircle) :
    ∃ r : ℝ, (r : UnitAddCircle) = t ∧ |r| ≤ 1 / 2 ∧ ‖t‖ = |r| := by
  obtain ⟨x⟩ := t
  have hz : (((round x : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff _).2
    exact ⟨round x, by simp⟩
  refine ⟨x - round x, ?_, abs_sub_round x, UnitAddCircle.norm_eq⟩
  simp [hz]
  rfl

lemma chord_real (r : ℝ) :
    ‖circleEmbed (r : UnitAddCircle) - 1‖ = 2 * |Real.sin (Real.pi * r)| := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp]
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hr : 2 * Real.pi * r / 2 = Real.pi * r := by ring
  rw [hr, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma chord_bounds (t : UnitAddCircle) :
    4 * ‖t‖ ≤ ‖circleEmbed t - 1‖ ∧
    ‖circleEmbed t - 1‖ ≤ (2 * Real.pi) * ‖t‖ := by
  obtain ⟨r, rfl, hr, hn⟩ := circle_rep t
  rw [chord_real, hn]
  have habs : |Real.pi * r| = Real.pi * |r| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hb : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [habs]; nlinarith [Real.pi_pos]
  have hlo := Real.mul_abs_le_abs_sin hb
  have hhi := Real.abs_sin_le_abs (x := Real.pi * r)
  rw [habs] at hlo hhi
  have hcalc : 2 / Real.pi * (Real.pi * |r|) = 2 * |r| := by
    field_simp
  rw [hcalc] at hlo
  constructor <;> nlinarith

lemma circleEmbed_add (s t : UnitAddCircle) :
    circleEmbed (s + t) = circleEmbed s * circleEmbed t := by
  exact congrArg (fun c : Circle => (c : ℂ)) (AddCircle.toCircle_add s t)

@[simp] lemma circleEmbed_norm (t : UnitAddCircle) : ‖circleEmbed t‖ = 1 :=
  (AddCircle.toCircle t).norm_coe

lemma chord_sub (s t : UnitAddCircle) :
    ‖circleEmbed s - circleEmbed t‖ = ‖circleEmbed (s - t) - 1‖ := by
  have hmul : circleEmbed (s - t) * circleEmbed t = circleEmbed s := by
    rw [← circleEmbed_add, sub_add_cancel]
  have heq : circleEmbed s - circleEmbed t =
      (circleEmbed (s - t) - 1) * circleEmbed t := by
    rw [sub_mul, one_mul, hmul]
  rw [heq, norm_mul, circleEmbed_norm, mul_one]

lemma chord_sub_bounds (s t : UnitAddCircle) :
    4 * ‖s - t‖ ≤ ‖circleEmbed s - circleEmbed t‖ ∧
    ‖circleEmbed s - circleEmbed t‖ ≤ (2 * Real.pi) * ‖s - t‖ := by
  rw [chord_sub]
  exact chord_bounds (s - t)

lemma memlp_circle_iff_complex (p : ℝ≥0∞) (x y : ℕ → UnitAddCircle) :
    Memℓp (fun n => x n - y n) p ↔
    Memℓp (fun n => circleEmbed (x n) - circleEmbed (y n)) p := by
  constructor
  · intro h
    exact (h.norm.const_mul (2 * Real.pi)).mono fun n => (chord_sub_bounds _ _).2
  · intro h
    apply (h.norm.const_mul (1 / 4 : ℝ)).mono
    intro n
    have := (chord_sub_bounds (x n) (y n)).1
    linarith

lemma memlp_complex_iff_re_im (p : ℝ≥0∞) (z : ℕ → ℂ) :
    Memℓp z p ↔ Memℓp (fun n => (z n).re) p ∧ Memℓp (fun n => (z n).im) p := by
  constructor
  · intro h
    constructor
    · exact h.norm.mono fun n => Complex.abs_re_le_norm (z n)
    · exact h.norm.mono fun n => Complex.abs_im_le_norm (z n)
  · rintro ⟨hr, hi⟩
    exact (hr.norm.add hi.norm).mono fun n => Complex.norm_le_abs_re_add_abs_im (z n)

def pairCoords (a b : ℕ → ℝ) (i : ℕ × Fin 2) : ℝ :=
  if i.2 = 0 then a i.1 else b i.1

def interleave (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  pairCoords a b (Nat.divModEquiv 2 n)

@[simp] lemma interleave_even (a b : ℕ → ℝ) (n : ℕ) :
    interleave a b (2 * n) = a n := by
  simp [interleave, pairCoords, Nat.divModEquiv, Nat.mul_comm]

@[simp] lemma interleave_odd (a b : ℕ → ℝ) (n : ℕ) :
    interleave a b (2 * n + 1) = b n := by
  simp [interleave, pairCoords, Nat.divModEquiv, Nat.mul_comm]
  have hd : (n * 2 + 1) / 2 = n := by omega
  have hm : ¬ 2 ∣ n * 2 + 1 := by omega
  simp [hm, hd]

lemma interleave_sub (a b c d : ℕ → ℝ) :
    interleave a b - interleave c d = interleave (a - c) (b - d) := by
  ext n
  simp only [interleave, pairCoords, Pi.sub_apply]
  split_ifs <;> rfl

lemma memlp_interleave (p : ℝ≥0∞) (hp : 0 < p.toReal) (a b : ℕ → ℝ) :
    Memℓp (interleave a b) p ↔ Memℓp a p ∧ Memℓp b p := by
  simp only [memℓp_gen_iff hp]
  change Summable ((fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal) ∘
    Nat.divModEquiv 2) ↔ _
  rw [(Nat.divModEquiv 2).summable_iff]
  constructor
  · intro h
    constructor
    · simpa [Function.comp_def, pairCoords] using
        h.comp_injective (f := fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal)
          (i := fun n : ℕ => (n, (0 : Fin 2))) (by intro n m h; exact congrArg Prod.fst h)
    · simpa [Function.comp_def, pairCoords] using
        h.comp_injective (f := fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal)
          (i := fun n : ℕ => (n, (1 : Fin 2))) (by intro n m h; exact congrArg Prod.fst h)
  · rintro ⟨ha, hb⟩
    apply (summable_prod_of_nonneg (by intro i; positivity)).2
    constructor
    · intro n
      exact (hasSum_fintype (fun j : Fin 2 => ‖pairCoords a b (n, j)‖ ^ p.toReal)).summable
    · simpa [tsum_fintype, Fin.sum_univ_two, pairCoords] using ha.add hb

def realEmbed (x : ℕ → UnitAddCircle) : ℕ → ℝ :=
  interleave (fun n => (circleEmbed (x n)).re) (fun n => (circleEmbed (x n)).im)

lemma continuous_realEmbed : Continuous realEmbed := by
  apply continuous_pi
  intro n
  dsimp [realEmbed, interleave, pairCoords]
  split_ifs
  · exact Complex.continuous_re.comp (continuous_circleEmbed.comp (continuous_apply _))
  · exact Complex.continuous_im.comp (continuous_circleEmbed.comp (continuous_apply _))

@[simp] lemma realEmbed_even (x : ℕ → UnitAddCircle) (n : ℕ) :
    realEmbed x (2 * n) = (circleEmbed (x n)).re := by simp [realEmbed]

@[simp] lemma realEmbed_odd (x : ℕ → UnitAddCircle) (n : ℕ) :
    realEmbed x (2 * n + 1) = (circleEmbed (x n)).im := by simp [realEmbed]

def CircleLpRel (p : ℝ≥0∞) (x y : ℕ → UnitAddCircle) : Prop :=
  Memℓp (fun n => x n - y n) p

def RealLpRel (p : ℝ≥0∞) (x y : ℕ → ℝ) : Prop :=
  Memℓp (fun n => x n - y n) p

theorem circle_real_lp_reduction (p : ℝ≥0∞) (hp : 0 < p.toReal)
    (x y : ℕ → UnitAddCircle) :
    CircleLpRel p x y ↔ RealLpRel p (realEmbed x) (realEmbed y) := by
  rw [CircleLpRel, memlp_circle_iff_complex, memlp_complex_iff_re_im]
  change _ ↔ Memℓp (realEmbed x - realEmbed y) p
  rw [realEmbed, realEmbed, interleave_sub, memlp_interleave p hp]
  rfl

lemma null_circle_iff_complex (x y : ℕ → UnitAddCircle) :
    Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
    Tendsto (fun n => circleEmbed (x n) - circleEmbed (y n)) atTop (𝓝 0) := by
  conv_lhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro h
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (chord_sub_bounds (x n) (y n)).2)
    simpa using h.const_mul (2 * Real.pi)
  · intro h
    apply squeeze_zero (fun n => norm_nonneg _)
      (g := fun n => (1 / 4 : ℝ) * ‖circleEmbed (x n) - circleEmbed (y n)‖)
    · intro n
      have := (chord_sub_bounds (x n) (y n)).1
      linarith
    · simpa using h.const_mul (1 / 4 : ℝ)

lemma null_interleave (a b : ℕ → ℝ) :
    Tendsto (interleave a b) atTop (𝓝 0) ↔
    Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) := by
  simp only [Metric.tendsto_atTop]
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n) (by omega)
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n + 1) (by omega)
  · rintro ⟨ha, hb⟩ ε hε
    obtain ⟨Na, hNa⟩ := ha ε hε
    obtain ⟨Nb, hNb⟩ := hb ε hε
    refine ⟨2 * max Na Nb, fun n hn => ?_⟩
    have hna : Na ≤ n / 2 := by omega
    have hnb : Nb ≤ n / 2 := by omega
    change dist (if (Nat.divModEquiv 2 n).2 = 0 then a (n / 2) else b (n / 2)) 0 < ε
    split_ifs
    · exact hNa _ hna
    · exact hNb _ hnb

def CircleNullRel (x y : ℕ → UnitAddCircle) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

def RealNullRel (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

theorem circle_real_null_reduction (x y : ℕ → UnitAddCircle) :
    CircleNullRel x y ↔ RealNullRel (realEmbed x) (realEmbed y) := by
  rw [CircleNullRel, null_circle_iff_complex]
  change _ ↔ Tendsto (realEmbed x - realEmbed y) atTop (𝓝 0)
  rw [realEmbed, realEmbed, interleave_sub, null_interleave]
  constructor
  · intro h
    constructor
    · change Tendsto (fun n => (circleEmbed (x n)).re - (circleEmbed (y n)).re) atTop (𝓝 0)
      simpa only [Function.comp_def, Complex.sub_re, Complex.zero_re] using
        Complex.continuous_re.continuousAt.tendsto.comp h
    · change Tendsto (fun n => (circleEmbed (x n)).im - (circleEmbed (y n)).im) atTop (𝓝 0)
      simpa only [Function.comp_def, Complex.sub_im, Complex.zero_im] using
        Complex.continuous_im.continuousAt.tendsto.comp h
  · rintro ⟨hr, hi⟩
    apply tendsto_zero_iff_norm_tendsto_zero.2
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => Complex.norm_le_abs_re_add_abs_im _)
    simpa using hr.norm.add hi.norm

/-- The concrete cos/sin interleaving reduces the real-exponent summability relations. -/
theorem circle_real_lp_reduction_real (p : ℝ) (hp : 1 ≤ p)
    (x y : ℕ → UnitAddCircle) :
    (Summable fun n => ‖x n - y n‖ ^ p) ↔
    Summable (fun n => |realEmbed x n - realEmbed y n| ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have hpt : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp0]
    linarith
  simpa only [CircleLpRel, RealLpRel, memℓp_gen_iff hpt,
    ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using
    circle_real_lp_reduction (ENNReal.ofReal p) hpt x y

/-- A single continuous map works for every finite real exponent p >= 1 and for c0. -/
theorem compact_circle_reductions :
    ∃ b : (ℕ → UnitAddCircle) → (ℕ → ℝ), Continuous b ∧
      (∀ p : ℝ, 1 ≤ p → ∀ x y,
        (Summable fun n => ‖x n - y n‖ ^ p) ↔
        Summable (fun n => |b x n - b y n| ^ p)) ∧
      (∀ x y, Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
        Tendsto (fun n => b x n - b y n) atTop (𝓝 0)) := by
  exact ⟨realEmbed, continuous_realEmbed, circle_real_lp_reduction_real,
    circle_real_null_reduction⟩

#print axioms chord_sub_bounds
#print axioms continuous_realEmbed
#print axioms circle_real_lp_reduction_real
#print axioms circle_real_null_reduction
#print axioms compact_circle_reductions

end MeasureEquivalenceCircleReduction
