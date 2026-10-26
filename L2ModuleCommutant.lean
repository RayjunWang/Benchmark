import MeasureUnitaryDensity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.Holder

/-! A bounded operator commuting with measurable multiplication
projections has an essentially bounded multiplier as its value at one.
This is a concrete L² module lemma for the finite-corner construction. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

theorem indicatorL2_norm_sq {s : Set α} (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖indicatorL2 μ hs f‖ ^ 2 = ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  rw [l2_norm_sq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem indicatorL2_one_norm_sq {s : Set α} (hs : MeasurableSet s) :
    ‖indicatorL2 μ hs (constantOneL2 μ)‖ ^ 2 = μ.real s := by
  rw [indicatorL2_norm_sq]
  calc
    (∫ x in s, ‖constantOneL2 μ x‖ ^ 2 ∂μ) = ∫ _ in s, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (constantOneL2_coe μ)] with x hx
      simp [hx]
    _ = μ.real s := by simp

theorem projectionCommutant_value_bound (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∀ᵐ x ∂μ, ‖T (constantOneL2 μ) x‖ ≤ ‖T‖ := by
  let u := T (constantOneL2 μ)
  have hi : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hsq : (fun x => ‖u x‖ ^ 2) ≤ᵐ[μ] fun _ => ‖T‖ ^ 2 := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const (‖T‖ ^ 2))
    intro s hs _
    rw [← indicatorL2_norm_sq μ hs u]
    change ‖indicatorL2 μ hs (T (constantOneL2 μ))‖ ^ 2 ≤ _
    rw [← hT]
    have hn := T.le_opNorm (indicatorL2 μ hs (constantOneL2 μ))
    calc
      ‖T (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2 ≤
          (‖T‖ * ‖indicatorL2 μ hs (constantOneL2 μ)‖) ^ 2 := by
        nlinarith [norm_nonneg (T (indicatorL2 μ hs (constantOneL2 μ))),
          mul_nonneg (norm_nonneg T) (norm_nonneg (indicatorL2 μ hs (constantOneL2 μ)))]
      _ = ‖T‖ ^ 2 * μ.real s := by rw [mul_pow, indicatorL2_one_norm_sq]
      _ = ∫ _ in s, ‖T‖ ^ 2 ∂μ := by simp [mul_comm]
  filter_upwards [hsq] with x hx
  change ‖T (constantOneL2 μ) x‖ ≤ ‖T‖
  change ‖T (constantOneL2 μ) x‖ ^ 2 ≤ ‖T‖ ^ 2 at hx
  nlinarith [norm_nonneg T, norm_nonneg (T (constantOneL2 μ) x)]

theorem projectionCommutant_value_memLp_top (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    MemLp (fun x => T (constantOneL2 μ) x) ∞ μ :=
  memLp_top_of_bound (Lp.aestronglyMeasurable _) ‖T‖
    (projectionCommutant_value_bound μ T hT)

theorem constantVectorL2_eq_smul_one (c : ℂ) :
    constantVectorL2 μ c = c • constantOneL2 μ := by
  apply Lp.ext
  filter_upwards [constantVectorL2_coe μ c, constantOneL2_coe μ,
    Lp.coeFn_smul c (constantOneL2 μ)] with x hc h1 hsmul
  rw [hc, hsmul]
  simp [h1]

theorem indicatorConstLp_eq_indicator_one {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : ℂ) :
    indicatorConstLp 2 hs hμs c = indicatorL2 μ hs (constantVectorL2 μ c) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c),
    indicatorL2_coe μ hs (constantVectorL2 μ c), constantVectorL2_coe μ c]
      with x hleft hright hc
  rw [hleft, hright]
  by_cases hx : x ∈ s <;> simp [hx, hc]

theorem projectionCommutant_determined_by_one (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      S (indicatorL2 μ hs f) = indicatorL2 μ hs (S f))
    (hone : T (constantOneL2 μ) = S (constantOneL2 μ)) : T = S := by
  have hfun : (T : Lp ℂ 2 μ → Lp ℂ 2 μ) = S := by
    apply Continuous.ext_on (Lp.simpleFunc.dense (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
      T.continuous S.continuous
    intro f hf
    lift f to Lp.simpleFunc ℂ 2 μ using hf
    induction f using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
    | @indicatorConst c s hs hμs =>
      dsimp only [Lp.simpleFunc.coe_indicatorConst]
      rw [indicatorConstLp_eq_indicator_one μ hs hμs.ne c, hT, hS]
      have hc : T (constantVectorL2 μ c) = S (constantVectorL2 μ c) := by
        rw [constantVectorL2_eq_smul_one, map_smul, map_smul, hone]
      rw [hc]
    | @add f g hf hg _ ihf ihg =>
      change T ((f.toLp hf : Lp ℂ 2 μ) + (g.toLp hg : Lp ℂ 2 μ)) =
        S ((f.toLp hf : Lp ℂ 2 μ) + (g.toLp hg : Lp ℂ 2 μ))
      rw [map_add, map_add, ihf, ihg]
  exact DFunLike.coe_injective hfun

omit [IsFiniteMeasure μ] in
noncomputable def boundedMultiplierL2 (b : Lp ℂ ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 b

omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_coe (b : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b f =ᵐ[μ] fun x => b x * f x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) b f

omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_indicator (b : Lp ℂ ∞ μ) {s : Set α} (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b (indicatorL2 μ hs f) =
      indicatorL2 μ hs (boundedMultiplierL2 μ b f) := by
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ b (indicatorL2 μ hs f),
    indicatorL2_coe μ hs f, indicatorL2_coe μ hs (boundedMultiplierL2 μ b f),
    boundedMultiplierL2_coe μ b f] with x hm hi ho hf
  rw [hm, hi, ho]
  by_cases hx : x ∈ s <;> simp [hx, hf]

noncomputable def projectionCommutantSymbol (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) : Lp ℂ ∞ μ :=
  (projectionCommutant_value_memLp_top μ T hT).toLp (fun x => T (constantOneL2 μ) x)

theorem projectionCommutantSymbol_coe (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    projectionCommutantSymbol μ T hT =ᵐ[μ] fun x => T (constantOneL2 μ) x :=
  (projectionCommutant_value_memLp_top μ T hT).coeFn_toLp

theorem projectionCommutant_eq_multiplier (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    T = boundedMultiplierL2 μ (projectionCommutantSymbol μ T hT) := by
  apply projectionCommutant_determined_by_one μ T _ hT
    (fun _ hs f => boundedMultiplierL2_indicator μ _ hs f)
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT)
      (constantOneL2 μ), projectionCommutantSymbol_coe μ T hT, constantOneL2_coe μ]
    with x hm hs h1
  rw [hm, hs, h1, mul_one]

end MeasureUnitary

#print axioms MeasureUnitary.projectionCommutant_value_bound
#print axioms MeasureUnitary.projectionCommutant_value_memLp_top
#print axioms MeasureUnitary.projectionCommutant_determined_by_one
#print axioms MeasureUnitary.projectionCommutant_eq_multiplier
