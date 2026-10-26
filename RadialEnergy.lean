import RadialRetraction
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic

/-! Finite-dimensional radial energy estimates. Scalar Poincaré
inequalities for the truncated coordinates imply the vector truncated
energy inequality. Neither the original vector nor its displacement
is required to be integrable. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkRadialEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma continuous_radial {R : ℝ} (hR : 0 < R) : Continuous (BenchmarkRadial.radial R : E → E) := by
  apply Continuous.smul _ continuous_id
  apply continuous_const.div (continuous_const.max continuous_norm)
  intro v
  exact (lt_of_lt_of_le hR (le_max_left _ _)).ne'

lemma norm_radial_eq_min {R : ℝ} (hR : 0 < R) (v : E) :
    ‖BenchmarkRadial.radial R v‖ = min ‖v‖ R := by
  by_cases hv : ‖v‖ ≤ R
  · rw [BenchmarkRadial.radial_eq_self hR hv, min_eq_left hv]
  · have hnv : 0 < ‖v‖ := lt_of_lt_of_le hR (le_of_not_ge hv)
    rw [BenchmarkRadial.radial, max_eq_right (le_of_not_ge hv), min_eq_right (le_of_not_ge hv),
      norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hnv)]
    exact div_mul_cancel₀ _ hnv.ne'

lemma min_rpow (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (min a b) ^ q = min (a ^ q) (b ^ q) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, min_eq_left (Real.rpow_le_rpow ha hab hq)]
  · rw [min_eq_right hba, min_eq_right (Real.rpow_le_rpow hb hba hq)]

lemma radial_energy_bound {R q : ℝ} (hR : 0 < R) (hq : 0 ≤ q) (v w : E) :
    ENNReal.ofReal (‖BenchmarkRadial.radial R v - BenchmarkRadial.radial R w‖ ^ q) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q) * ENNReal.ofReal (min (‖v - w‖ ^ q) (R ^ q)) := by
  have hb := Real.rpow_le_rpow (norm_nonneg _)
    (BenchmarkRadial.norm_radial_sub_le_two_min hR v w) hq
  rw [Real.mul_rpow (by norm_num) (le_min (norm_nonneg _) hR.le),
    min_rpow _ _ _ (norm_nonneg _) hR.le hq] at hb
  have he := ENNReal.ofReal_le_ofReal hb
  rwa [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at he

variable {I : Type*} [Fintype I] (p : ℝ≥0∞) [Fact (1 ≤ p)]

abbrev Vector := PiLp p (fun _ : I => ℝ)

def scalarEnergy (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (|r| ^ p.toReal)
def vectorEnergy (v : Vector (I := I) p) : ℝ≥0∞ := ENNReal.ofReal (‖v‖ ^ p.toReal)

lemma norm_rpow_eq_sum (hp : p ≠ ∞) (v : Vector (I := I) p) :
    ‖v‖ ^ p.toReal = ∑ i, |v i| ^ p.toReal := by
  have hpos : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  rw [PiLp.norm_eq_sum hpos, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) ]
  rw [one_div_mul_cancel hpos.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

lemma vectorEnergy_eq_sum (hp : p ≠ ∞) (v : Vector (I := I) p) :
    vectorEnergy p v = ∑ i, scalarEnergy p (v i) := by
  unfold vectorEnergy scalarEnergy
  rw [norm_rpow_eq_sum p hp]
  exact ENNReal.ofReal_sum_of_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

variable {X S : Type*} [MeasurableSpace X] [Fintype S] (μ : Measure X)

lemma integral_vectorEnergy (hp : p ≠ ∞) (v : X → Vector (I := I) p) (hv : Measurable v) :
    (∫⁻ x, vectorEnergy p (v x) ∂μ) = ∑ i, ∫⁻ x, scalarEnergy p (v x i) ∂μ := by
  simp_rw [vectorEnergy_eq_sum p hp]
  apply lintegral_finsetSum
  intro i _
  exact ((((PiLp.continuous_apply p (β := fun _ : I => ℝ) i).measurable.comp hv).abs).pow_const _).ennreal_ofReal

/-- This is the finite-prefix truncated-energy inequality obtained by adding
the scalar Poincaré inequalities for the radial coordinates. -/
theorem truncated_energy_from_scalar
    (hp : p ≠ ∞) {R : ℝ} (hR : 0 < R) (C : ℝ≥0∞)
    (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (v : X → Vector (I := I) p) (hv : Measurable v)
    (hscalar : ∀ i : I,
      (∫⁻ x, scalarEnergy p (BenchmarkRadial.radial R (v x) i) ∂μ) ≤
        C * ∑ s : S, ∫⁻ x, scalarEnergy p
          (BenchmarkRadial.radial R (v (t s x)) i - BenchmarkRadial.radial R (v x) i) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p.toReal) * C *
        ∑ s : S, ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
  classical
  let u := fun x => BenchmarkRadial.radial R (v x)
  have hu : Measurable u := continuous_radial hR |>.measurable.comp hv
  have hleft : (∫⁻ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) =
      ∑ i, ∫⁻ x, scalarEnergy p (u x i) ∂μ := by
    rw [← integral_vectorEnergy p μ hp u hu]
    congr 1
    funext x
    unfold vectorEnergy
    rw [norm_radial_eq_min hR, min_rpow _ _ _ (norm_nonneg _) hR.le ENNReal.toReal_nonneg]
  have hmiddle : (∑ i, C * ∑ s : S, ∫⁻ x, scalarEnergy p (u (t s x) i - u x i) ∂μ) =
      C * ∑ s : S, ∫⁻ x, vectorEnergy p (u (t s x) - u x) ∂μ := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    exact (integral_vectorEnergy p μ hp (fun x => u (t s x) - u x)
      ((hu.comp (ht s)).sub hu)).symm
  have hbound : ∀ s : S,
      (∫⁻ x, vectorEnergy p (u (t s x) - u x) ∂μ) ≤
        ENNReal.ofReal ((2 : ℝ) ^ p.toReal) *
          ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
    intro s
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    exact radial_energy_bound hR ENNReal.toReal_nonneg (v (t s x)) (v x)
  calc
    _ = ∑ i, ∫⁻ x, scalarEnergy p (u x i) ∂μ := hleft
    _ ≤ ∑ i, C * ∑ s : S, ∫⁻ x, scalarEnergy p (u (t s x) i - u x i) ∂μ :=
      Finset.sum_le_sum fun i _ => hscalar i
    _ = C * ∑ s : S, ∫⁻ x, vectorEnergy p (u (t s x) - u x) ∂μ := hmiddle
    _ ≤ C * ∑ s : S, ENNReal.ofReal ((2 : ℝ) ^ p.toReal) *
        ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ :=
      mul_le_mul_left' (Finset.sum_le_sum fun s _ => hbound s) C
    _ = _ := by rw [← Finset.mul_sum]; ac_rfl

end BenchmarkRadialEnergy

#print axioms BenchmarkRadialEnergy.truncated_energy_from_scalar
