import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Scalar finite-product estimate

This file verifies only an elementary scalar estimate used in a Fourier argument.
It does not formalize Parseval's identity, the trigonometric multiplier bound,
or any theorem about Borel reducibility or equivalence of measures.
-/

open scoped BigOperators

namespace MeasureEquivalenceScalar

/-- A reciprocal form of Bernoulli's inequality, proved by induction. -/
theorem reciprocal_bernoulli (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (1 + (n : ℝ) * a) * (1 - a) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 - a) ^ n := pow_nonneg (sub_nonneg.mpr ha1) _
    calc
      (1 + ((n + 1 : ℕ) : ℝ) * a) * (1 - a) ^ (n + 1) =
          ((1 + (n : ℝ) * a) - ((n : ℝ) + 1) * a ^ 2) * (1 - a) ^ n := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ (1 + (n : ℝ) * a) * (1 - a) ^ n := by
        apply mul_le_mul_of_nonneg_right _ hp
        have hsq : 0 ≤ ((n : ℝ) + 1) * a ^ 2 := by positivity
        linarith
      _ ≤ 1 := ih

/-- The quantitative loss in a power, valid when the total loss is at most one. -/
theorem power_loss (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (hna : (n : ℝ) * a ≤ 1) :
    (1 - a) ^ n ≤ 1 - (n : ℝ) * a / 2 := by
  have hx0 : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
  have hx2 : ((n : ℝ) * a) ^ 2 ≤ (n : ℝ) * a := by nlinarith
  have hden : 0 < 1 + (n : ℝ) * a := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  calc
    (1 + (n : ℝ) * a) * (1 - a) ^ n ≤ 1 := reciprocal_bernoulli a ha ha1 n
    _ ≤ (1 + (n : ℝ) * a) * (1 - (n : ℝ) * a / 2) := by nlinarith

/--
If every scalar has absolute value at most one and `t.card` marked scalars
have absolute value at most `1-a`, the product loses at least `t.card*a/2`.
The factors may be negative, and both finite sets may be empty.
-/
theorem finite_product_loss {ι : Type*} (s t : Finset ι) (q : ι → ℝ) (a : ℝ)
    (hts : t ⊆ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : ∀ i ∈ s, |q i| ≤ 1)
    (hmarked : ∀ i ∈ t, |q i| ≤ 1 - a)
    (hra : (t.card : ℝ) * a ≤ 1) :
    (t.card : ℝ) * a / 2 ≤ 1 - ∏ i ∈ s, q i := by
  have hprod : (∏ i ∈ s, q i) ≤ (1 - a) ^ t.card := by
    calc
      (∏ i ∈ s, q i) ≤ |∏ i ∈ s, q i| := le_abs_self _
      _ = ∏ i ∈ s, |q i| := Finset.abs_prod s q
      _ ≤ ∏ i ∈ t, |q i| :=
        Finset.prod_le_prod_of_subset_of_le_one hts
          (fun i _ => abs_nonneg (q i)) (fun i hi _ => hq i hi)
      _ ≤ ∏ _i ∈ t, (1 - a) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg (q i)) hmarked
      _ = (1 - a) ^ t.card := by simp
  have hp := power_loss a ha ha1 t.card hra
  linarith

/--
Specialization to the multiplier loss `a = 1/m^2`.  The parameter `m` is real,
so this also applies to positive integer torus sizes after coercion.
-/
theorem square_scale_multiplier {ι : Type*} (s t : Finset ι) (q : ι → ℝ) (m : ℝ)
    (hts : t ⊆ s) (hm : 1 ≤ m)
    (hq : ∀ i ∈ s, |q i| ≤ 1)
    (hmarked : ∀ i ∈ t, |q i| ≤ 1 - 1 / m ^ 2)
    (hr : (t.card : ℝ) ≤ m ^ 2) :
    4 * (t.card : ℝ) ≤ 4 * m ^ 2 * (2 * (1 - ∏ i ∈ s, q i)) := by
  have hmpos : 0 < m := by linarith
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hmpos
  have hm2one : 1 ≤ m ^ 2 := by nlinarith
  have ha0 : 0 ≤ 1 / m ^ 2 := by positivity
  have ha1 : 1 / m ^ 2 ≤ 1 := (div_le_one hm2pos).mpr hm2one
  have hra : (t.card : ℝ) * (1 / m ^ 2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hm2pos).mpr hr
  have h := finite_product_loss s t q (1 / m ^ 2) hts ha0 ha1 hq hmarked hra
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hm2pos)
  field_simp [ne_of_gt hmpos] at hmul
  nlinarith

end MeasureEquivalenceScalar

#print axioms MeasureEquivalenceScalar.finite_product_loss
#print axioms MeasureEquivalenceScalar.square_scale_multiplier
