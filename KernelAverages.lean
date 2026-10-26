import OrbitMarkov
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Actual bounded kernel iterates, Cesaro averages, and almost-everywhere
subsequences of their Hilbert mean-ergodic limits. -/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

noncomputable def kernelApply (P : Kernel Z Z) (f : Z → ℝ) (z : Z) : ℝ := ∫ y, f y ∂P z

noncomputable def kernelIterate (P : Kernel Z Z) (f : Z → ℝ) : ℕ → Z → ℝ
  | 0 => f
  | n + 1 => kernelApply P (kernelIterate P f n)

noncomputable def kernelAverage (P : Kernel Z Z) (f : Z → ℝ) (n : ℕ) (z : Z) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ range n, kernelIterate P f k z

theorem kernelApply_measurable (P : Kernel Z Z) (f : Z → ℝ) (hf : Measurable f) :
    Measurable (kernelApply P f) := hf.stronglyMeasurable.integral_kernel.measurable

theorem kernelIterate_measurable (P : Kernel Z Z) (f : Z → ℝ) (hf : Measurable f) :
    ∀ n, Measurable (kernelIterate P f n) := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => exact kernelApply_measurable P _ ih

theorem kernelAverage_measurable (P : Kernel Z Z) (f : Z → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (kernelAverage P f n) :=
  measurable_const.mul (Finset.measurable_sum _ (fun k _ => kernelIterate_measurable P f hf k))

theorem kernelApply_abs_le (P : Kernel Z Z) [IsMarkovKernel P]
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ z, |kernelApply P f z| ≤ C := by
  intro z
  have hfi : Integrable f (P z) := Integrable.mono' (integrable_const C)
    hf.aestronglyMeasurable (Eventually.of_forall (fun y => by simpa using hfC y))
  calc
    _ ≤ ∫ y, ‖f y‖ ∂P z := norm_integral_le_integral_norm f
    _ ≤ ∫ _ : Z, C ∂P z := integral_mono hfi.norm (integrable_const C) (fun y => by simpa using hfC y)
    _ = C := by simp

theorem kernelIterate_abs_le (P : Kernel Z Z) [IsMarkovKernel P]
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ n z, |kernelIterate P f n z| ≤ C := by
  intro n
  induction n with
  | zero => exact hfC
  | succ n ih => exact kernelApply_abs_le P _ (kernelIterate_measurable P f hf n) C hC ih

theorem kernelAverage_abs_le (P : Kernel Z Z) [IsMarkovKernel P]
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ n z, |kernelAverage P f n z| ≤ C := by
  intro n z
  by_cases hn : n = 0
  · simpa [kernelAverage, hn] using hC
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsum : |∑ k ∈ range n, kernelIterate P f k z| ≤ (n : ℝ) * C := by
    calc
      _ ≤ ∑ k ∈ range n, |kernelIterate P f k z| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ range n, C := sum_le_sum (fun k _ => kernelIterate_abs_le P f hf C hC hfC k z)
      _ = (n : ℝ) * C := by simp
  rw [kernelAverage, abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * C) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C := by field_simp

theorem kernelApply_congr_ae (μ : Measure Z) (P : Kernel Z Z)
    (hstationary : P ∘ₘ μ = μ) {f g : Z → ℝ} (hfg : f =ᵐ[μ] g) :
    kernelApply P f =ᵐ[μ] kernelApply P g := by
  have h := Measure.ae_ae_of_ae_comp (by rwa [hstationary] : f =ᵐ[P ∘ₘ μ] g)
  exact h.mono (fun z hz => integral_congr_ae hz)

theorem kernelApply_integral_of_stationary (ν : Measure Z) [SFinite ν] (P : Kernel Z Z)
    [IsSFiniteKernel P] (hstationary : P ∘ₘ ν = ν)
    (f : Z → ℝ) (hf : Integrable f ν) :
    (∫ z, kernelApply P f z ∂ν) = ∫ z, f z ∂ν := by
  have hfi : Integrable f ((P ∘ₖ Kernel.const Unit ν) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, hstationary]
    exact hf
  have h := ProbabilityTheory.Kernel.integral_comp hfi
  simpa only [← Measure.comp_eq_comp_const_apply, hstationary, Kernel.const_apply] using h.symm

theorem kernelIterate_setIntegral (ν : Measure Z) [IsFiniteMeasure ν]
    (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ n, (∫ z in s, kernelIterate P f n z ∂ν) = ∫ z in s, f z ∂ν := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ z in s, kernelApply P (kernelIterate P f n) z ∂ν) = _
    rw [kernelApply_integral_of_stationary (ν.restrict s) P hstationary]
    · exact ih
    · apply Integrable.mono' (integrable_const C)
        (kernelIterate_measurable P f hf n).aestronglyMeasurable
      exact Eventually.of_forall (fun z => by
        simpa using kernelIterate_abs_le P f hf C hC hfC n z)

theorem kernelAverage_setIntegral (ν : Measure Z) [IsFiniteMeasure ν]
    (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C)
    (n : ℕ) (hn : n ≠ 0) :
    (∫ z in s, kernelAverage P f n z ∂ν) = ∫ z in s, f z ∂ν := by
  have hI (k : ℕ) : Integrable (kernelIterate P f k) (ν.restrict s) := by
    apply Integrable.mono' (integrable_const C) (kernelIterate_measurable P f hf k).aestronglyMeasurable
    exact Eventually.of_forall (fun z => by simpa using kernelIterate_abs_le P f hf C hC hfC k z)
  unfold kernelAverage
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hI k)]
  simp_rw [kernelIterate_setIntegral ν P s hstationary f hf C hC hfC]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- Dominated convergence transfers the constant limit of actual kernel
averages to the invariant-set integral identities needed for ergodicity. -/
theorem setIntegral_eq_mul_of_kernelAverage_limit
    (ν : Measure Z) [IsFiniteMeasure ν] (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C)
    (ns : ℕ → ℕ) (hns : StrictMono ns) (c : ℝ)
    (hlimit : ∀ᵐ z ∂ν, Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 c)) :
    (∫ z in s, f z ∂ν) = c * ν.real s := by
  have ht : Tendsto (fun n => ∫ z in s, kernelAverage P f (ns n) z ∂ν)
      atTop (𝓝 (∫ _z in s, c ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (kernelAverage_measurable P f hf (ns n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun z => by simpa using kernelAverage_abs_le P f hf C hC hfC (ns n) z)
    · exact ae_restrict_of_ae hlimit
  have hconst : (fun n => ∫ z in s, kernelAverage P f (ns n) z ∂ν) =ᶠ[atTop]
      fun _ => ∫ z in s, f z ∂ν := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : ns n ≠ 0 := by
      intro hz
      have hid : n ≤ ns n := hns.id_le n
      rw [hz] at hid
      omega
    exact kernelAverage_setIntegral ν P s hstationary f hf C hC hfC (ns n) hn0
  have hconstlim : Tendsto (fun n => ∫ z in s, kernelAverage P f (ns n) z ∂ν)
      atTop (𝓝 (∫ z in s, f z ∂ν)) := tendsto_const_nhds.congr' hconst.symm
  have heq := tendsto_nhds_unique ht hconstlim
  rw [setIntegral_const, smul_eq_mul, mul_comm] at heq
  exact heq.symm

private theorem lp_finset_sum_coe (μ : Measure Z) {ι : Type*}
    (s : Finset ι) (u : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, u i : Lp ℝ 2 μ) =ᵐ[μ] fun z => ∑ i ∈ s, u i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (μ := μ) (E := ℝ) (p := 2))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with z hz hsum
    simpa only [Pi.add_apply, Finset.sum_insert ha] using hz.trans (congrArg (fun v => u a z + v) hsum)

section L2

variable (μ : Measure Z) (P : Kernel Z Z)
    (hstationary : P ∘ₘ μ = μ)
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hL : ∀ f : Lp ℝ 2 μ, L f =ᵐ[μ] kernelApply P f)

include hstationary hL

theorem iterate_ae_eq_kernelIterate (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∀ n, (L^[n] (hf.toLp f)) =ᵐ[μ] kernelIterate P f n := by
  intro n
  induction n with
  | zero => exact hf.coeFn_toLp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hL _).trans (kernelApply_congr_ae μ P hstationary ih)

theorem birkhoffAverage_ae_eq_kernelAverage (f : Z → ℝ) (hf : MemLp f 2 μ) (n : ℕ) :
    (birkhoffAverage ℝ L id n (hf.toLp f) : Lp ℝ 2 μ) =ᵐ[μ] kernelAverage P f n := by
  have hall := ae_all_iff.mpr (iterate_ae_eq_kernelIterate μ P hstationary L hL f hf)
  unfold birkhoffAverage birkhoffSum
  simp only [id_eq]
  filter_upwards [hall,
    Lp.coeFn_smul (n : ℝ)⁻¹ (∑ k ∈ range n, L^[k] (hf.toLp f)),
    lp_finset_sum_coe μ (range n) (fun k => L^[k] (hf.toLp f))] with z hz hsm hsum
  rw [hsm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  unfold kernelAverage
  congr 1
  exact sum_congr rfl (fun k _ => hz k)

/-- A genuine almost-everywhere subsequence of the Hilbert mean-ergodic
limit, written in terms of the actual pointwise kernel averages. -/
theorem exists_kernelAverage_subseq_tendsto_ae
    (hLnorm : ‖L‖ ≤ 1) (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂μ, Tendsto (fun n => kernelAverage P f (ns n) z) atTop
        (𝓝 (((LinearMap.eqLocus L 1).orthogonalProjection (hf.toLp f) : Lp ℝ 2 μ) z)) := by
  have ht := L.tendsto_birkhoffAverage_orthogonalProjection hLnorm (hf.toLp f)
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr (birkhoffAverage_ae_eq_kernelAverage μ P hstationary L hL f hf)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hAE, hall] with z hz heq
  exact hz.congr' (Eventually.of_forall (fun n => heq (ns n)))

end L2

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.kernelAverage_abs_le
#print axioms MeasureEquivalenceMarkov.birkhoffAverage_ae_eq_kernelAverage
#print axioms MeasureEquivalenceMarkov.exists_kernelAverage_subseq_tendsto_ae
#print axioms MeasureEquivalenceMarkov.setIntegral_eq_mul_of_kernelAverage_limit
