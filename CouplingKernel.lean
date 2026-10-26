import CouplingMarkov
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The L2 coupling transition is the actual pointwise kernel integral. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal InnerProduct

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

theorem couplingTransition_setIntegral (f : Lp ℝ 2 μ) (s : Set Z) (hs : MeasurableSet s) :
    (∫ z in s, couplingTransition μ J hfst hsnd f z ∂μ) =
      ∫ z in Prod.fst ⁻¹' s, f z.2 ∂J := by
  let hpf : MeasurePreserving Prod.fst J μ := ⟨measurable_fst, hfst⟩
  let hps : MeasurePreserving Prod.snd J μ := ⟨measurable_snd, hsnd⟩
  let I : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)
  calc
    _ = inner ℝ I (couplingTransition μ J hfst hsnd f) :=
      (L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) _).symm
    _ = inner ℝ (couplingFirst μ J hfst I) (couplingSecond μ J hsnd f) := by
      change inner ℝ I ((couplingFirst μ J hfst).toContinuousLinearMap.adjoint
        ((couplingSecond μ J hsnd).toContinuousLinearMap f)) = _
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ∫ z in Prod.fst ⁻¹' s, couplingSecond μ J hsnd f z ∂J := by
      change inner ℝ (Lp.compMeasurePreserving Prod.fst hpf I) _ = _
      rw [Lp.indicatorConstLp_compMeasurePreserving hs (measure_ne_top μ s) (1 : ℝ) hpf]
      exact L2.inner_indicatorConstLp_one (hs.preimage measurable_fst) _ _
    _ = _ := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving f hps)

/-- Whenever a stationary coupling is represented by a genuine kernel,
the adjoint-defined L2 contraction agrees almost everywhere with its
pointwise integral. This supplies the common functional formula needed
to compare the same transition on conditional component measures. -/
theorem couplingTransition_ae_eq_integral_kernel
    (κ : Kernel Z Z) [IsFiniteKernel κ] (hJ : J = μ ⊗ₘ κ)
    (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f =ᵐ[μ] fun z => ∫ y, f y ∂κ z := by
  have hfμ : Integrable f μ := MemLp.integrable (by norm_num) (Lp.memLp f)
  have hPfμ : Integrable (couplingTransition μ J hfst hsnd f) μ :=
    MemLp.integrable (by norm_num) (Lp.memLp _)
  have hfJ : Integrable (fun z : Z × Z => f z.2) J :=
    (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩).integrable_comp_of_integrable hfμ
  have hstationary : κ ∘ₘ μ = μ := by
    rw [← Measure.snd_compProd, ← hJ]
    exact hsnd
  have hfcomp : Integrable f (κ ∘ₘ μ) := by rwa [hstationary]
  have hnormI := Measure.integrable_integral_norm_of_integrable_comp hfcomp
  have hkernelI : Integrable (fun z => ∫ y, f y ∂κ z) μ := by
    apply Integrable.mono' hnormI (Lp.stronglyMeasurable f).integral_kernel.aestronglyMeasurable
    exact Eventually.of_forall (fun z => norm_integral_le_integral_norm _)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hPfμ hkernelI
  intro s hs _
  rw [couplingTransition_setIntegral μ J hfst hsnd f s hs]
  have hset : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set Z) := by ext z; simp
  rw [hset, hJ]
  rw [Measure.setIntegral_compProd hs MeasurableSet.univ (by simpa [← hJ] using hfJ.integrableOn)]
  simp

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.couplingTransition_setIntegral
#print axioms MeasureEquivalenceMarkov.couplingTransition_ae_eq_integral_kernel
