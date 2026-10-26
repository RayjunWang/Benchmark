import PoincareRadial
import Mathlib.Probability.CDF

/-! Actual finite medians for real random variables, obtained from the
right-continuous cumulative distribution function. -/

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkRealMedians

open BenchmarkPoincareRadial

theorem exists_real_distribution_median (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ m : ℝ, ν (Iio m) ≤ 1 / 2 ∧ ν (Ioi m) ≤ 1 / 2 := by
  let A : Set ℝ := {x | (1 / 2 : ℝ) ≤ cdf ν x}
  have hne : A.Nonempty := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
    exact ⟨b, hb.le⟩
  have hbelow : BddBelow A := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atBot ν).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    refine ⟨b, fun a ha => ?_⟩
    by_contra hba
    have hlt : a < b := lt_of_not_ge hba
    have hmono := (monotone_cdf ν) hlt.le
    exact (not_lt_of_ge (ha.trans hmono)) hb
  let m := sInf A
  have hmright : (1 / 2 : ℝ) ≤ cdf ν m := by
    rw [← (cdf ν).iInf_Ioi_eq m]
    apply le_ciInf
    intro r
    obtain ⟨a, ha, har⟩ := (csInf_lt_iff hbelow hne).mp r.property
    exact ha.trans ((monotone_cdf ν) har.le)
  have hmleft : Function.leftLim (cdf ν) m ≤ (1 / 2 : ℝ) := by
    have hfilter : 𝓝[<] m ≠ ⊥ := by rw [← neBot_iff]; infer_instance
    rw [(monotone_cdf ν).leftLim_eq_sSup hfilter]
    apply csSup_le
    · exact ⟨cdf ν (m - 1), m - 1, by simp, rfl⟩
    · rintro z ⟨a, ha, rfl⟩
      have hnot : ¬ (1 / 2 : ℝ) ≤ cdf ν a := by
        intro haa
        have hma : m ≤ a := csInf_le hbelow haa
        exact not_le_of_gt ha hma
      exact (lt_of_not_ge hnot).le
  refine ⟨m, ?_, ?_⟩
  · have heq : ν (Iio m) = ENNReal.ofReal (Function.leftLim (cdf ν) m) := by
      calc
        ν (Iio m) = (cdf ν).measure (Iio m) := by rw [measure_cdf]
        _ = _ := by rw [(cdf ν).measure_Iio (tendsto_cdf_atBot ν), sub_zero]
    rw [heq]
    calc
      ENNReal.ofReal (leftLim (cdf ν) m) ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hmleft
      _ = 1 / 2 := by norm_num [ENNReal.ofReal_div_of_pos]
  · have heq : ν (Ioi m) = ENNReal.ofReal (1 - cdf ν m) := by
      calc
        ν (Ioi m) = (cdf ν).measure (Ioi m) := by rw [measure_cdf]
        _ = _ := by rw [(cdf ν).measure_Ioi (tendsto_cdf_atTop ν)]
    rw [heq]
    calc
      ENNReal.ofReal (1 - cdf ν m) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = 1 / 2 := by norm_num [ENNReal.ofReal_div_of_pos]

theorem exists_zeroMedian {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, ZeroMedian μ (fun x => f x - m) := by
  let ν := μ.map f
  haveI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨m, hn, hp⟩ := exists_real_distribution_median ν
  refine ⟨m, ?_, ?_⟩
  · have heq : {x | f x - m < 0} = f ⁻¹' Iio m := by ext x; simp
    rw [heq, ← Measure.map_apply hf measurableSet_Iio]
    simpa only [measure_univ] using hn
  · have heq : {x | 0 < f x - m} = f ⁻¹' Ioi m := by ext x; simp
    rw [heq, ← Measure.map_apply hf measurableSet_Ioi]
    simpa only [measure_univ] using hp

theorem exists_coordinate_medians {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℕ → ℝ) (hf : Measurable f) :
    ∃ m : ℕ → ℝ, ∀ i, ZeroMedian μ (fun x => f x i - m i) := by
  have hex : ∀ i : ℕ, ∃ m : ℝ, ZeroMedian μ (fun x => f x i - m) :=
    fun i => exists_zeroMedian μ (fun x => f x i) ((measurable_pi_apply i).comp hf)
  exact Classical.axiom_of_choice hex

end BenchmarkRealMedians

#print axioms BenchmarkRealMedians.exists_coordinate_medians
