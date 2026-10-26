import RestrictedCompatibility
import RestrictedDeparture
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem tsum_departureProbability_ne_top (h : ℕ → ℝ)
    (hh : Summable (fun n => |h n|)) : (∑' n, departureProbability (h n)) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum (fun n => departureProbability_le (h n)))
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top (by norm_num) hh.tsum_ofReal_ne_top

theorem tsum_departureProbability_eq_top (h : ℕ → ℝ)
    (hh : ¬ Summable (fun n => |h n|)) : (∑' n, departureProbability (h n)) = ∞ := by
  by_contra hsum
  apply hh
  have hm : (∑' n, ENNReal.ofReal (min 1 |h n|)) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum (fun n => departureProbability_lower (h n)))
  have hreal : Summable (fun n => min 1 |h n|) :=
    (ENNReal.summable_toReal hm).congr (fun n =>
      ENNReal.toReal_ofReal (le_min zero_le_one (abs_nonneg (h n))))
  have hev : ∀ᶠ n in atTop, min 1 |h n| < 1 :=
    hreal.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)
  apply hreal.congr_atTop
  filter_upwards [hev] with n hn
  exact min_eq_right ((min_lt_iff.mp hn).resolve_left (lt_irrefl _)).le

theorem ae_shift_mem_tailProbability (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    ∀ᵐ x ∂tailProbability, x + h ∈ restrictedProductSpace := by
  let A : ℕ → Set RealSequences := fun n => {x | x n ∈ departureSet (h n)}
  have hA (n : ℕ) : tailProbability (A n) = departureProbability (h n) := by
    have hm : tailProbability.map (fun x => x n) = baseMeasure :=
      Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) n
    change tailProbability ((fun x : RealSequences => x n) ⁻¹' departureSet (h n)) = _
    rw [← Measure.map_apply (measurable_pi_apply n) (measurable_departureSet (h n)), hm]
    rfl
  have hsum : (∑' n, tailProbability (A n)) ≠ ∞ := by
    simp_rw [hA]
    exact tsum_departureProbability_ne_top h hh
  filter_upwards [ae_eventually_notMem hsum, ae_base_tailProbability] with x hx hi
  obtain ⟨N, hN⟩ := eventually_atTop.mp hx
  apply mem_iUnion.mpr
  refine ⟨N, ?_⟩
  intro n hn
  have hnot : ¬ (x n ∈ baseInterval ∧ x n + h n ∉ baseInterval) := hN n hn
  exact not_not.mp (fun hbad => hnot ⟨hi n, hbad⟩)

theorem ae_shift_mem_stageMeasure (h : RealSequences)
    (hh : Summable (fun n => |h n|)) (n : ℕ) :
    ∀ᵐ x ∂stageMeasure n, x + h ∈ restrictedProductSpace := by
  let t : RealSequences := fun k => h (n + k)
  have ht : Summable (fun k => |t k|) :=
    hh.comp_injective (by intro i j hij; exact Nat.add_left_cancel hij)
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    ((measurable_id.add_const h) measurable_restrictedProductSpace)).mpr
  apply (Measure.ae_prod_iff_ae_ae
    (((measurable_id.add_const h).comp (headTailEquiv n).symm.measurable)
      measurable_restrictedProductSpace)).mpr
  apply ae_of_all
  intro head
  filter_upwards [ae_shift_mem_tailProbability t ht] with tail htail
  obtain ⟨M, hM⟩ := mem_iUnion.mp htail
  apply mem_iUnion.mpr
  refine ⟨n + M, ?_⟩
  intro k hk
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ k)
  have hr : M ≤ r := by omega
  simpa only [Function.comp_apply, id_eq, Pi.add_apply, headTailEquiv_symm_tail, t] using hM r hr

theorem ae_shift_mem_restrictedProductMeasure (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    ∀ᵐ x ∂restrictedProductMeasure, x + h ∈ restrictedProductSpace := by
  rw [ae_iff]
  change restrictedProductStages.limit {x | x + h ∉ restrictedProductSpace} = 0
  have hbad : MeasurableSet {x : RealSequences | x + h ∉ restrictedProductSpace} :=
    ((show Measurable (fun x : RealSequences => x + h) from by fun_prop)
      measurable_restrictedProductSpace).compl
  rw [restrictedProductStages.limit_apply _ hbad]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  exact ae_shift_mem_stageMeasure h hh n

theorem map_shift_restrictedProductMeasure_compl (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    (restrictedProductMeasure.map (fun x => x + h)) restrictedProductSpaceᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) measurable_restrictedProductSpace.compl]
  exact ae_shift_mem_restrictedProductMeasure h hh

theorem ae_shift_not_mem_tailProbability (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) :
    ∀ᵐ x ∂tailProbability, x + h ∉ restrictedProductSpace := by
  let A : ℕ → Set RealSequences := fun n => {x | x n ∈ departureSet (h n)}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurable_pi_apply n) (measurable_departureSet (h n))
  have hA (n : ℕ) : tailProbability (A n) = departureProbability (h n) := by
    have hm : tailProbability.map (fun x => x n) = baseMeasure :=
      Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) n
    change tailProbability ((fun x : RealSequences => x n) ⁻¹' departureSet (h n)) = _
    rw [← Measure.map_apply (measurable_pi_apply n) (measurable_departureSet (h n)), hm]
    rfl
  have hi : ProbabilityTheory.iIndepSet A tailProbability := by
    apply (ProbabilityTheory.iIndepSet_iff_meas_biInter hAm).mpr
    intro s
    have he : (⋂ i ∈ s, A i) = Set.pi s (fun i => departureSet (h i)) := by
      ext x
      simp [A, Set.mem_pi]
    rw [he]
    change Measure.infinitePi (fun _ : ℕ => baseMeasure)
      (Set.pi s (fun i => departureSet (h i))) = _
    rw [Measure.infinitePi_pi (fun _ : ℕ => baseMeasure) (fun i _ => measurable_departureSet (h i))]
    exact Finset.prod_congr rfl (fun i _ => (hA i).symm)
  have hsum : (∑' n, tailProbability (A n)) = ∞ := by
    simp_rw [hA]
    exact tsum_departureProbability_eq_top h hh
  have hprob := ProbabilityTheory.measure_limsup_eq_one hAm hi hsum
  have hae : ∀ᵐ x ∂tailProbability, x ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hAm)).mpr hprob
  filter_upwards [hae] with x hx
  have hfreq := mem_limsup_iff_frequently_mem.mp hx
  intro hX
  obtain ⟨N, hN⟩ := mem_iUnion.mp hX
  have hev : ∀ᶠ k in atTop, x k + h k ∈ baseInterval := eventually_atTop.mpr ⟨N, hN⟩
  obtain ⟨k, hk, hki⟩ := (hfreq.and_eventually hev).exists
  exact hk.2 hki

theorem ae_shift_not_mem_stageMeasure (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) (n : ℕ) :
    ∀ᵐ x ∂stageMeasure n, x + h ∉ restrictedProductSpace := by
  let t : RealSequences := fun k => h (n + k)
  have ht : ¬ Summable (fun k => |t k|) := by
    intro hs
    apply hh
    have hs' : Summable (fun k => |h (k + n)|) := by simpa [t, Nat.add_comm] using hs
    exact Summable.comp_nat_add (f := fun k => |h k|) (k := n) hs'
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    (((measurable_id.add_const h) measurable_restrictedProductSpace).compl)).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((((measurable_id.add_const h).comp (headTailEquiv n).symm.measurable)
      measurable_restrictedProductSpace).compl)).mpr
  apply ae_of_all
  intro head
  filter_upwards [ae_shift_not_mem_tailProbability t ht] with tail htail
  intro hX
  obtain ⟨M, hM⟩ := mem_iUnion.mp hX
  apply htail
  apply mem_iUnion.mpr
  refine ⟨M, ?_⟩
  intro r hr
  have hh' := hM (n + r) (by omega)
  simpa only [Function.comp_apply, id_eq, Pi.add_apply, headTailEquiv_symm_tail, t] using hh'

theorem map_shift_restrictedProductMeasure_null (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) :
    (restrictedProductMeasure.map (fun x => x + h)) restrictedProductSpace = 0 := by
  rw [Measure.map_apply (by fun_prop) measurable_restrictedProductSpace]
  change restrictedProductStages.limit {x | x + h ∈ restrictedProductSpace} = 0
  have hm : MeasurableSet {x : RealSequences | x + h ∈ restrictedProductSpace} :=
    (show Measurable (fun x : RealSequences => x + h) from by fun_prop)
      measurable_restrictedProductSpace
  rw [restrictedProductStages.limit_apply _ hm]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  have he := ae_iff.mp (ae_shift_not_mem_stageMeasure h hh n)
  simpa only [not_not] using he

theorem map_shift_mutuallySingular_of_not_summable (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) :
    restrictedProductMeasure.map (fun x => x + h) ⟂ₘ restrictedProductMeasure :=
  ⟨restrictedProductSpace, measurable_restrictedProductSpace,
    map_shift_restrictedProductMeasure_null h hh, restrictedProductMeasure_compl⟩

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.map_shift_restrictedProductMeasure_compl
#print axioms MeasureEquivalenceRestrictedProduct.map_shift_mutuallySingular_of_not_summable
