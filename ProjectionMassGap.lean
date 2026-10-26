import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

noncomputable section

namespace BenchmarkProjectionGap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem projection_mass_variation (P : H →L[ℝ] H)
    (hP : ∀ w, ‖P w‖ ≤ ‖w‖) (u v : H) (huv : ‖u‖ = ‖v‖) :
    ‖P u‖ ^ 2 - ‖P v‖ ^ 2 ≤ 2 * ‖v‖ * ‖u - v‖ := by
  have hd : ‖P u‖ - ‖P v‖ ≤ ‖u - v‖ := by
    calc
      ‖P u‖ - ‖P v‖ ≤ ‖P u - P v‖ := norm_sub_norm_le _ _
      _ = ‖P (u - v)‖ := by rw [map_sub]
      _ ≤ ‖u - v‖ := hP _
  have hs : ‖P u‖ + ‖P v‖ ≤ 2 * ‖v‖ := by
    have h1 := hP u
    have h2 := hP v
    rw [huv] at h1
    linarith
  calc
    ‖P u‖ ^ 2 - ‖P v‖ ^ 2 = (‖P u‖ - ‖P v‖) * (‖P u‖ + ‖P v‖) := by ring
    _ ≤ ‖u - v‖ * (‖P u‖ + ‖P v‖) :=
      mul_le_mul_of_nonneg_right hd (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖u - v‖ * (2 * ‖v‖) := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = 2 * ‖v‖ * ‖u - v‖ := by ring

theorem two_partition_gap (Pap Pam Pbp Pbm : H →L[ℝ] H)
    (hap : ∀ w, ‖Pap w‖ ≤ ‖w‖) (hbp : ∀ w, ‖Pbp w‖ ≤ ‖w‖)
    (v uA uB : H) (hA : ‖uA‖ = ‖v‖) (hB : ‖uB‖ = ‖v‖)
    (hpairA : ‖Pap uA‖ ^ 2 + ‖Pam v‖ ^ 2 = ‖v‖ ^ 2)
    (hpairB : ‖Pbp uB‖ ^ 2 + ‖Pbm v‖ ^ 2 = ‖v‖ ^ 2)
    (hmass : ‖Pap v‖ ^ 2 + ‖Pam v‖ ^ 2 + ‖Pbp v‖ ^ 2 + ‖Pbm v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ‖v‖ ^ 2 ≤ 8 * (‖uA - v‖ ^ 2 + ‖uB - v‖ ^ 2) := by
  have hvarA := projection_mass_variation Pap hap uA v hA
  have hvarB := projection_mass_variation Pbp hbp uB v hB
  have hnorm : ‖v‖ ^ 2 ≤ 2 * ‖v‖ * (‖uA - v‖ + ‖uB - v‖) := by
    nlinarith
  by_cases hz : ‖v‖ = 0
  · rw [hz]
    nlinarith [sq_nonneg ‖uA - v‖, sq_nonneg ‖uB - v‖]
  · have hv : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hlin : ‖v‖ ≤ 2 * (‖uA - v‖ + ‖uB - v‖) := by nlinarith
    have hs := sq_nonneg (‖uA - v‖ - ‖uB - v‖)
    have hproduct := mul_self_le_mul_self (norm_nonneg v) hlin
    nlinarith

end BenchmarkProjectionGap

#print axioms BenchmarkProjectionGap.two_partition_gap
