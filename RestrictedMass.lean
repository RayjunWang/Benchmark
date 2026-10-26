import RestrictedSupport
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Set Filter
open scoped ENNReal Topology NNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def tailStaySet (h : RealSequences) (N : ℕ) : Set RealSequences :=
  {x | ∀ k, x k + h (N + k) ∈ baseInterval}

def tailStayProbability (h : RealSequences) (N : ℕ) : ℝ≥0∞ :=
  tailProbability (tailStaySet h N)

theorem measurable_tailStaySet (h : RealSequences) (N : ℕ) :
    MeasurableSet (tailStaySet h N) := by
  simpa only [tailStaySet, Set.setOf_forall] using MeasurableSet.iInter (fun k : ℕ =>
    ((measurable_pi_apply k).add_const (h (N + k)))
      (show MeasurableSet baseInterval from measurableSet_Icc))

theorem exponentialMeasure_add_preimage (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    exponentialMeasure ((fun t : ℝ => t + a) ⁻¹' s) =
      ENNReal.ofReal (Real.exp a) * exponentialMeasure s := by
  have he := congrArg (fun μ : Measure ℝ => μ s) (map_add_exponentialMeasure a)
  dsimp only at he
  rw [Measure.map_apply (by fun_prop) hs, Measure.smul_apply, smul_eq_mul] at he
  exact he

theorem fin_prod_ofReal_exp (n : ℕ) (h : RealSequences) :
    (∏ i : Fin n, ENNReal.ofReal (Real.exp (h i))) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, h i)) := by
  simp only [← coe_expNNReal, ← ENNReal.coe_finsetProd]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_prod, expNNReal, Real.exp_sum]
  rfl

theorem shifted_stage_base_mass (h : RealSequences) (n : ℕ) :
    ((stageMeasure n).map (fun x => x + h)) (stageSet 0) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, h i)) * tailStayProbability h n := by
  let H : Set (Fin n → ℝ) := Set.univ.pi (fun i => (fun t : ℝ => t + h i) ⁻¹' baseInterval)
  have hpre : ((fun x : RealSequences => x + h) ∘ (headTailEquiv n).symm) ⁻¹'
      stageSet 0 = H ×ˢ tailStaySet h n := by
    ext z
    change (∀ k, 0 ≤ k → (headTailEquiv n).symm z k + h k ∈ baseInterval) ↔
      ((∀ i : Fin n, i ∈ Set.univ → z.1 i + h i ∈ baseInterval) ∧
        ∀ k, z.2 k + h (n + k) ∈ baseInterval)
    constructor
    · intro hz
      constructor
      · intro i _
        simpa only [headTailEquiv_symm_head] using hz (i : ℕ) (Nat.zero_le _)
      · intro k
        simpa only [headTailEquiv_symm_tail] using hz (n + k) (Nat.zero_le _)
    · rintro ⟨hh, ht⟩ k _
      by_cases hk : k < n
      · rw [headTailEquiv_symm_head n z ⟨k, hk⟩]
        exact hh ⟨k, hk⟩ (mem_univ _)
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hk)
        simpa only [headTailEquiv_symm_tail] using ht r
  unfold stageMeasure
  rw [Measure.map_map (by fun_prop) (headTailEquiv n).symm.measurable,
    Measure.map_apply (by fun_prop) (measurable_stageSet 0), hpre, Measure.prod_prod]
  change (Measure.pi (fun _ : Fin n => exponentialMeasure)) H * tailStayProbability h n = _
  dsimp only [H]
  rw [Measure.pi_pi]
  simp_rw [exponentialMeasure_add_preimage _ baseInterval
    (show MeasurableSet baseInterval from measurableSet_Icc), exponentialMeasure_baseInterval,
    mul_one]
  rw [fin_prod_ofReal_exp]

theorem tailStayProbability_le_one (h : RealSequences) (N : ℕ) :
    tailStayProbability h N ≤ 1 := prob_le_one

def eventualStaySet (h : RealSequences) (N : ℕ) : Set RealSequences :=
  {x | ∀ k, N ≤ k → x k + h k ∈ baseInterval}

theorem measurable_eventualStaySet (h : RealSequences) (N : ℕ) :
    MeasurableSet (eventualStaySet h N) := by
  simpa only [eventualStaySet, Set.setOf_forall] using MeasurableSet.iInter (fun k : ℕ =>
    MeasurableSet.iInter (fun _ : N ≤ k =>
      ((measurable_pi_apply k).add_const (h k))
        (show MeasurableSet baseInterval from measurableSet_Icc)))

theorem tailStayProbability_eq_eventual (h : RealSequences) (N : ℕ) :
    tailStayProbability h N = tailProbability (eventualStaySet h N) := by
  have hm : tailProbability.map (fun x k => x (N + k)) = tailProbability :=
    Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => baseMeasure) (f := fun k => N + k)
      (fun _ _ hij => Nat.add_left_cancel hij)
  unfold tailStayProbability
  conv_lhs => rw [← hm]
  rw [Measure.map_apply (by fun_prop) (measurable_tailStaySet h N)]
  congr 1
  ext x
  constructor
  · intro hx k hk
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hx r
  · intro hx k
    exact hx (N + k) (Nat.le_add_right _ _)

theorem tendsto_tailStayProbability (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    Tendsto (tailStayProbability h) atTop (𝓝 1) := by
  have hmono : Monotone (eventualStaySet h) := by
    intro n m hnm x hx k hmk
    exact hx k (hnm.trans hmk)
  have hae : ∀ᵐ x ∂tailProbability, x ∈ ⋃ N, eventualStaySet h N := by
    filter_upwards [ae_shift_mem_tailProbability h hh] with x hx
    obtain ⟨N, hN⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨N, hN⟩
  have hmass : tailProbability (⋃ N, eventualStaySet h N) = 1 :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (measurable_eventualStaySet h))).mp hae
  have ht := tendsto_measure_iUnion_atTop (μ := tailProbability) hmono
  rw [hmass] at ht
  have he : (tailProbability ∘ eventualStaySet h) = tailStayProbability h := by
    funext N
    exact (tailStayProbability_eq_eventual h N).symm
  rw [he] at ht
  exact ht

theorem shifted_restricted_base_mass (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    (restrictedProductMeasure.map (fun x => x + h)) (stageSet 0) =
      ENNReal.ofReal (Real.exp (∑' n, h n)) := by
  have hs : Summable h := summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using hh)
  have hscalar : Tendsto (fun N => ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range N, h k)))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (∑' n, h n)))) :=
    ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp hs.hasSum.tendsto_sum_nat)
  have hlim := ENNReal.Tendsto.mul hscalar
    (Or.inr (by norm_num : (1 : ℝ≥0∞) ≠ ∞))
    (tendsto_tailStayProbability h hh)
    (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0))
  simp only [mul_one] at hlim
  rw [Measure.map_apply (by fun_prop) (measurable_stageSet 0)]
  change restrictedProductStages.limit ((fun x : RealSequences => x + h) ⁻¹' stageSet 0) = _
  rw [restrictedProductStages.limit_apply _
    ((show Measurable (fun x : RealSequences => x + h) from by fun_prop) (measurable_stageSet 0))]
  apply iSup_eq_of_tendsto
  · intro n m hnm
    exact restrictedProductStages.monotone_measure hnm _
  · have hseq (N : ℕ) : restrictedProductStages.measure N
        ((fun x : RealSequences => x + h) ⁻¹' stageSet 0) =
        ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range N, h k)) * tailStayProbability h N := by
      change stageMeasure N ((fun x : RealSequences => x + h) ⁻¹' stageSet 0) = _
      rw [← Measure.map_apply (by fun_prop) (measurable_stageSet 0), shifted_stage_base_mass,
        Fin.sum_univ_eq_sum_range]
    simpa only [hseq] using hlim

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.shifted_stage_base_mass
#print axioms MeasureEquivalenceRestrictedProduct.shifted_restricted_base_mass
