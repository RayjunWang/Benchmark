import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalitiesPow

/-! Elementary power estimates used to transfer the Hilbert gap to every finite exponent. -/

open Set

noncomputable section

namespace BenchmarkPowerDifference

theorem abs_sub_rpow_le {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : |a ^ q - b ^ q| ≤ |a - b| ^ q := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm] using this hb ha (le_of_not_ge hab)
  have hpow := Real.rpow_add_le_add_rpow hb (sub_nonneg.mpr hab) hq0 hq1
  have hmon := Real.rpow_le_rpow hb hab hq0
  rw [add_sub_cancel] at hpow
  rw [abs_of_nonneg (sub_nonneg.mpr hmon), abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

theorem abs_sub_rpow_le_lipschitz {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 1 ≤ q) : |a ^ q - b ^ q| ≤ q * (max a b) ^ (q - 1) * |a - b| := by
  have hd (x : ℝ) (_ : x ∈ Icc 0 (max a b)) :
      HasDerivWithinAt (fun x : ℝ => x ^ q) (q * x ^ (q - 1)) (Icc 0 (max a b)) x :=
    (Real.hasDerivAt_rpow_const (Or.inr hq)).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Icc 0 (max a b)) :
      ‖q * x ^ (q - 1)‖ ≤ q * (max a b) ^ (q - 1) := by
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx.1 _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx.1 hx.2 (sub_nonneg.mpr hq)) (by linarith)
  have h := (convex_Icc 0 (max a b)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hbound ⟨hb, le_max_right _ _⟩ ⟨ha, le_max_left _ _⟩
  simpa only [Real.norm_eq_abs] using h

def powerErrorConstant (p : ℝ) : ℝ := p ^ 2 * (16 * p) ^ (p - 2)

theorem powerErrorConstant_nonneg (p : ℝ) (hp : 2 ≤ p) : 0 ≤ powerErrorConstant p := by
  unfold powerErrorConstant
  positivity

theorem power_difference_sq_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 2 ≤ p) :
    (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      (1 / 256 : ℝ) * (max a b) ^ p + powerErrorConstant p * |a - b| ^ p := by
  let M := max a b
  let d := |a - b|
  have hM : 0 ≤ M := le_trans ha (le_max_left _ _)
  have hd : 0 ≤ d := abs_nonneg _
  have hp0 : 0 < p := by linarith
  have he : 0 ≤ p - 2 := by linarith
  have hbasic := abs_sub_rpow_le_lipschitz ha hb (q := p / 2) (by linarith)
  have hsquare : (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      p ^ 2 * M ^ (p - 2) * d ^ 2 := by
    have hpow : (M ^ (p / 2 - 1)) ^ 2 = M ^ (p - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
      congr 1
      ring
    have hsq := sq_le_sq₀ (abs_nonneg (a ^ (p / 2) - b ^ (p / 2)))
      (mul_nonneg (mul_nonneg (by linarith : 0 ≤ p / 2) (Real.rpow_nonneg hM _)) hd) |>.mpr hbasic
    rw [sq_abs, mul_pow, mul_pow, hpow] at hsq
    have hn : 0 ≤ M ^ (p - 2) * d ^ 2 := by positivity
    dsimp only [M, d] at hsq ⊢
    nlinarith
  have hsum : M ^ (p - 2) * M ^ 2 = M ^ p := by
    rw [← Real.rpow_natCast M 2]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_add_of_nonneg hM he (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  by_cases hsmall : d ≤ M / (16 * p)
  · have hscale : d * (16 * p) ≤ M := (le_div_iff₀ (by positivity)).mp hsmall
    have hs : p ^ 2 * d ^ 2 ≤ M ^ 2 / 256 := by
      have hsqr := (sq_le_sq₀ (by positivity : 0 ≤ d * (16 * p)) hM).mpr hscale
      nlinarith
    have hbnd := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hM (p - 2))
    have hfinish : p ^ 2 * M ^ (p - 2) * d ^ 2 ≤ (1 / 256 : ℝ) * M ^ p := by
      rw [← hsum]
      nlinarith
    exact hsquare.trans (hfinish.trans (le_add_of_nonneg_right
      (mul_nonneg (powerErrorConstant_nonneg p hp) (Real.rpow_nonneg hd _))))
  · have hlarge : M ≤ (16 * p) * d := by
      have h := (div_lt_iff₀ (by positivity : 0 < 16 * p)).mp (lt_of_not_ge hsmall)
      linarith
    have hpow := Real.rpow_le_rpow hM hlarge he
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 16 * p) hd] at hpow
    have hsumd : d ^ (p - 2) * d ^ 2 = d ^ p := by
      rw [← Real.rpow_natCast d 2]
      norm_num only [Nat.cast_ofNat]
      rw [← Real.rpow_add_of_nonneg hd he (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg (sq_nonneg p) (sq_nonneg d))
    have hfinish : p ^ 2 * M ^ (p - 2) * d ^ 2 ≤ powerErrorConstant p * d ^ p := by
      unfold powerErrorConstant
      rw [← hsumd]
      nlinarith
    exact hsquare.trans (hfinish.trans (le_add_of_nonneg_left
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hM _))))

end BenchmarkPowerDifference

#print axioms BenchmarkPowerDifference.power_difference_sq_le
