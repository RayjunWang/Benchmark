import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The nonintegrable truncated-energy step

The final limiting argument of the spectral-gap homomorphism theorem is
proved here without assuming integrability of any cocycle norm. The input
is the normalized truncated-energy inequality. Deriving that inequality
from scalar Poincaré inequalities and radial truncation is a separate
formalization obligation.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace BenchmarkTruncatedEnergy

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (μ : Measure X) [IsFiniteMeasure μ]

def realClip (c : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (min (c / ((n : ℝ) + 1)) 1)

def energyClip (H : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  min (H * ENNReal.ofReal (1 / ((n : ℝ) + 1))) 1

lemma realClip_le_one (c : ℝ) (n : ℕ) : realClip c n ≤ 1 := by
  exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans (by norm_num)

lemma realClip_tendsto_zero (c : ℝ) :
    Tendsto (fun n => realClip c n) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := c)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [realClip, min_eq_left (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (hd.min (tendsto_const_nhds (x := (1 : ℝ))))

lemma energyClip_top (n : ℕ) : energyClip ∞ n = 1 := by
  have hp : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := ENNReal.ofReal_pos.mpr (by positivity)
  unfold energyClip
  rw [ENNReal.top_mul hp.ne']
  simp

lemma integral_realClip_tendsto_zero (c : X → ℝ) (hc : Measurable c) :
    Tendsto (fun n => ∫⁻ x, realClip (c x) n ∂μ) atTop (𝓝 0) := by
  have hm : ∀ n, Measurable (fun x => realClip (c x) n) := by
    intro n
    exact ((hc.div_const _).min measurable_const).ennreal_ofReal
  have hbound : ∀ n, (fun x => realClip (c x) n) ≤ᵐ[μ] fun _ => (1 : ℝ≥0∞) := by
    intro n
    exact ae_of_all μ (fun x => realClip_le_one (c x) n)
  have hfin : (∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ) ≠ ∞ := by simp
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => realClip (c x) n) atTop (𝓝 0) :=
    ae_of_all μ fun x => realClip_tendsto_zero (c x)
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence (fun _ : X => (1 : ℝ≥0∞)) hm hbound hfin hlim

/-- Finite cocycle energies have vanishing normalized truncations. The
energies need only be measurable real-valued functions, not integrable. -/
theorem ae_finite_of_truncated_energy
    (H : X → ℝ≥0∞) (hH : Measurable H)
    (c : S → X → ℝ) (hc : ∀ s, Measurable (c s))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ n : ℕ,
      (∫⁻ x, energyClip (H x) n ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ) :
    ∀ᵐ x ∂μ, H x ≠ ∞ := by
  classical
  let A : Set X := {x | H x = ∞}
  have hA : MeasurableSet A := hH (measurableSet_singleton ∞)
  have hbound : ∀ n : ℕ, μ A ≤ K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ := by
    intro n
    apply le_trans _ (henergy n)
    calc
      μ A = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by simp [hA]
      _ ≤ ∫⁻ x, energyClip (H x) n ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ A
        · rw [indicator_of_mem hx]
          have heq : H x = ∞ := hx
          change 1 ≤ energyClip (H x) n
          rw [heq, energyClip_top]
        · rw [indicator_of_notMem hx]
          exact bot_le
  have hsum : Tendsto (fun n => ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun s _ => integral_realClip_tendsto_zero μ (c s) (hc s))
  have hright : Tendsto (fun n => K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hsum (Or.inr hK)
  have hzero : μ A = 0 := le_antisymm (ge_of_tendsto hright (Eventually.of_forall hbound)) bot_le
  rw [ae_iff]
  simpa only [not_not] using hzero

end BenchmarkTruncatedEnergy

#print axioms BenchmarkTruncatedEnergy.ae_finite_of_truncated_energy
