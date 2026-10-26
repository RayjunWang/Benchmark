import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic

/-! The radial truncation estimate used in the all-finite-p spectral-gap
argument.  This holds in every real normed space and uses no integrability
hypothesis on the vector being truncated. -/

noncomputable section

namespace BenchmarkRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radial (R : ℝ) (v : E) : E := (R / max R ‖v‖) • v

theorem norm_radial_le {R : ℝ} (hR : 0 < R) (v : E) :
    ‖radial R v‖ ≤ R := by
  have hA : 0 < max R ‖v‖ := lt_of_lt_of_le hR (le_max_left _ _)
  have ha : 0 ≤ R / max R ‖v‖ := div_nonneg hR.le hA.le
  rw [radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    R / max R ‖v‖ * ‖v‖ ≤ R / max R ‖v‖ * max R ‖v‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ha
    _ = R := div_mul_cancel₀ _ hA.ne'

theorem radial_eq_self {R : ℝ} (hR : 0 < R) {v : E} (hv : ‖v‖ ≤ R) :
    radial R v = v := by
  simp [radial, max_eq_left hv, hR.ne']

lemma norm_radial_sub_le_ordered {R : ℝ} (hR : 0 < R) (v w : E)
    (hvw : ‖w‖ ≤ ‖v‖) :
    ‖radial R v - radial R w‖ ≤ 2 * ‖v - w‖ := by
  let A := max R ‖v‖
  let B := max R ‖w‖
  let a := R / A
  let b := R / B
  have hA : 0 < A := lt_of_lt_of_le hR (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le hR (le_max_left _ _)
  have hBA : B ≤ A := max_le_max_left R hvw
  have ha : 0 ≤ a := div_nonneg hR.le hA.le
  have ha1 : a ≤ 1 := (div_le_one hA).mpr (le_max_left _ _)
  have hab : a ≤ b := by
    change R / A ≤ R / B
    apply (div_le_div_iff₀ hA hB).mpr
    nlinarith
  have haA : a * A = R := div_mul_cancel₀ _ hA.ne'
  have hbB : b * B = R := div_mul_cancel₀ _ hB.ne'
  have hAB : A - B ≤ ‖v‖ - ‖w‖ := by
    dsimp [A, B]
    by_cases hv : ‖v‖ ≤ R
    · rw [max_eq_left hv, max_eq_left (hvw.trans hv)]
      linarith
    · rw [max_eq_right (le_of_not_ge hv)]
      have : ‖w‖ ≤ max R ‖w‖ := le_max_right _ _
      linarith
  have hD : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := norm_sub_norm_le v w
  have hterm : (b - a) * ‖w‖ ≤ ‖v - w‖ := by
    calc
      (b - a) * ‖w‖ ≤ (b - a) * B :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr hab)
      _ = a * (A - B) := by nlinarith [haA, hbB]
      _ ≤ A - B := by nlinarith [sub_nonneg.mpr hBA]
      _ ≤ ‖v - w‖ := hAB.trans hD
  have hdecomp : a • v - b • w = a • (v - w) + (a - b) • w := by
    simp only [smul_sub, sub_smul]
    abel
  change ‖a • v - b • w‖ ≤ _
  rw [hdecomp]
  calc
    ‖a • (v - w) + (a - b) • w‖ ≤ ‖a • (v - w)‖ + ‖(a - b) • w‖ := norm_add_le _ _
    _ = a * ‖v - w‖ + (b - a) * ‖w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    _ ≤ 2 * ‖v - w‖ := by nlinarith [norm_nonneg (v - w)]

theorem norm_radial_sub_le {R : ℝ} (hR : 0 < R) (v w : E) :
    ‖radial R v - radial R w‖ ≤ 2 * ‖v - w‖ := by
  rcases le_total ‖w‖ ‖v‖ with h | h
  · exact norm_radial_sub_le_ordered hR v w h
  · simpa only [norm_sub_rev] using norm_radial_sub_le_ordered hR w v h

theorem norm_radial_sub_le_two_radius {R : ℝ} (hR : 0 < R) (v w : E) :
    ‖radial R v - radial R w‖ ≤ 2 * R := by
  calc
    ‖radial R v - radial R w‖ ≤ ‖radial R v‖ + ‖radial R w‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith [norm_radial_le hR v, norm_radial_le hR w]

theorem norm_radial_sub_le_two_min {R : ℝ} (hR : 0 < R) (v w : E) :
    ‖radial R v - radial R w‖ ≤ 2 * min ‖v - w‖ R := by
  rcases le_total ‖v - w‖ R with h | h
  · rw [min_eq_left h]
    exact norm_radial_sub_le hR v w
  · rw [min_eq_right h]
    exact norm_radial_sub_le_two_radius hR v w

end BenchmarkRadial

#print axioms BenchmarkRadial.norm_radial_sub_le_two_min
