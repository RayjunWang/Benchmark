import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Trigonometric coordinate multiplier

This file checks the real-variable estimate used for each nonzero Fourier
coordinate.  In particular it applies to integer frequencies, without assuming
integrality.  It does not formalize the Fourier expansion or Parseval's identity.
-/

namespace MeasureEquivalenceTrig

/-- Jordan's inequality after scaling to a circle coordinate. -/
theorem scaled_jordan (m k : ℝ) (hm : 0 < m) (hk : 0 ≤ k)
    (hkm : k ≤ m / 2) :
    2 * k / m ≤ Real.sin (Real.pi * k / m) := by
  have hx0 : 0 ≤ Real.pi * k / m := by positivity
  have hx1 : Real.pi * k / m ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx1
  calc
    2 * k / m = 2 / Real.pi * (Real.pi * k / m) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ Real.sin (Real.pi * k / m) := h

/-- The sine is bounded away from zero throughout the central frequency range. -/
theorem sine_frequency_lower (m k : ℝ) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hkm1 : k ≤ m - 1) :
    2 / m ≤ Real.sin (Real.pi * k / m) := by
  have hmpos : 0 < m := by linarith
  by_cases hkhalf : k ≤ m / 2
  · have hj := scaled_jordan m k hmpos (by linarith) hkhalf
    have hleft : 2 / m ≤ 2 * k / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    exact hleft.trans hj
  · have hk' : 1 ≤ m - k := by linarith
    have hkhalf' : m - k ≤ m / 2 := by linarith
    have hj := scaled_jordan m (m - k) hmpos (by linarith) hkhalf'
    have hleft : 2 / m ≤ 2 * (m - k) / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    have hangle : Real.pi * (m - k) / m = Real.pi - Real.pi * k / m := by
      field_simp [ne_of_gt hmpos]
    rw [hangle, Real.sin_pi_sub] at hj
    exact hleft.trans hj

/--
The coordinate multiplier has a uniform absolute-value gap.  This is valid for
every real `m ≥ 2` and every real `k ∈ [1,m-1]`.
-/
theorem trig_coordinate_bound (m k : ℝ) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hkm1 : k ≤ m - 1) :
    |(1 + 2 * Real.cos (2 * Real.pi * k / m)) / 3| ≤ 1 - 1 / m ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hmpos
  have hs := sine_frequency_lower m k hm hk1 hkm1
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / m) hs 2
  have hsquare' : 4 * (1 / m ^ 2) ≤ Real.sin (Real.pi * k / m) ^ 2 := by
    convert hsquare using 1
    ring
  have hangle : 2 * Real.pi * k / m = 2 * (Real.pi * k / m) := by ring
  have hcos : Real.cos (2 * Real.pi * k / m) =
      1 - 2 * Real.sin (Real.pi * k / m) ^ 2 := by
    rw [hangle, Real.cos_two_mul_eq_one_sub]
  have hsmall : 1 / m ^ 2 ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ hm2pos (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hnonneg : 0 ≤ 1 / m ^ 2 := by positivity
  have hcoslower := Real.neg_one_le_cos (2 * Real.pi * k / m)
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

end MeasureEquivalenceTrig

#print axioms MeasureEquivalenceTrig.sine_frequency_lower
#print axioms MeasureEquivalenceTrig.trig_coordinate_bound
