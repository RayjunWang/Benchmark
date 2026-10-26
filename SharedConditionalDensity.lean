import HellingerKernel
import InvariantConditional

/-! The actual invariant conditional probabilities share the ambient
Radon--Nikodym derivatives. No unbounded-density kernel is postulated. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceSharedDensity

section Push

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

theorem map_withDensity_comp (M : Measure Z) (j : Z → W) (hj : Measurable j)
    (F : W → ℝ≥0∞) (hF : Measurable F) :
    (M.withDensity (fun z => F (j z))).map j = (M.map j).withDensity F := by
  ext s hs
  rw [Measure.map_apply hj hs, withDensity_apply _ (hs.preimage hj), withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage hj), ← lintegral_indicator hs,
    lintegral_map (hF.indicator hs) hj]
  rfl

end Push

section Joint

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (β : Measure Y) [IsFiniteMeasure β] (M : Measure Z) [IsFiniteMeasure M]
    (κ : Kernel Y Z) [IsFiniteKernel κ] (q : Z → Y) (hq : Measurable q)
    (hJ : β ⊗ₘ κ = M.map (fun z => (q z,z)))

include hq hJ in
theorem shared_rnDeriv_of_joint (f : Z → Z) (hf : Measurable f)
    (hJf : β ⊗ₘ κ.map f = (M.map f).map (fun z => (q z,z)))
    (hns : M.map f ≪ M) :
    ∀ᵐ y ∂β, (fun z => ((κ y).map f).rnDeriv (κ y) z) =ᵐ[κ y]
      (fun z => (M.map f).rnDeriv M z) := by
  let r : Z → ℝ≥0∞ := (M.map f).rnDeriv M
  have hr : Measurable r := Measure.measurable_rnDeriv _ _
  have hD : M.withDensity r = M.map f := Measure.withDensity_rnDeriv_eq _ _ hns
  have hJD : β ⊗ₘ κ.map f = (β ⊗ₘ κ).withDensity (fun p => r p.2) := by
    calc
      _ = (M.map f).map (fun z => (q z,z)) := hJf
      _ = (M.withDensity r).map (fun z => (q z,z)) := congrArg
        (Measure.map (fun z => (q z,z))) hD.symm
      _ = (M.map (fun z => (q z,z))).withDensity (fun p => r p.2) :=
        map_withDensity_comp M (fun z => (q z,z)) (hq.prodMk measurable_id)
          (fun p => r p.2) (hr.comp measurable_snd)
      _ = _ := congrArg (fun ν : Measure (Y × Z) => ν.withDensity (fun p => r p.2)) hJ.symm
  have hAC : β ⊗ₘ κ.map f ≪ β ⊗ₘ κ := by
    rw [hJD]
    exact withDensity_absolutelyContinuous _ _
  have hfib : ∀ᵐ y ∂β, (κ.map f) y ≪ κ y :=
    Measure.absolutelyContinuous_compProd_right_iff.mp hAC
  have hRK := MeasureEquivalenceHellinger.joint_rnDeriv_of_kernel_ac_ae β (κ.map f) κ hfib
  have hRg : (β ⊗ₘ κ.map f).rnDeriv (β ⊗ₘ κ) =ᵐ[β ⊗ₘ κ] fun p => r p.2 := by
    have h := (β ⊗ₘ κ).rnDeriv_withDensity (hr.comp measurable_snd)
    change ((β ⊗ₘ κ).withDensity (fun p => r p.2)).rnDeriv (β ⊗ₘ κ) =ᵐ[β ⊗ₘ κ]
      (fun p => r p.2) at h
    rw [← hJD] at h
    exact h
  have hker := Measure.ae_ae_of_ae_compProd (hRK.symm.trans hRg)
  filter_upwards [hker] with y hy
  have hmeasure := (κ.map f).rnDeriv_eq_rnDeriv_measure (η := κ) (a := y)
  simpa only [Kernel.map_apply _ hf] using hmeasure.symm.trans hy

end Joint

section Invariant

open MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

theorem invariantConditionalKernel_shared_rnDeriv (g : G)
    (hg : Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ᵐ x ∂μ,
      (fun z => ((invariantConditionalKernel (G := G) μ x).map (fun w => g • w)).rnDeriv
        (invariantConditionalKernel (G := G) μ x) z) =ᵐ[invariantConditionalKernel (G := G) μ x]
      (fun z => (μ.map (fun w => g • w)).rnDeriv μ z) := by
  have h := shared_rnDeriv_of_joint (μ.map (invariantBaseMap (G := G))) μ
    (invariantBaseKernel (G := G) μ) (invariantBaseMap (G := G))
    (invariantBaseMap_measurable (G := G)) (invariantBaseKernel_joint (G := G) μ)
    (fun z => g • z) hg.measurable (invariantBaseKernel_joint_map μ g hg.measurable)
    hg.absolutelyContinuous
  exact ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable h

end Invariant

end MeasureEquivalenceSharedDensity

#print axioms MeasureEquivalenceSharedDensity.shared_rnDeriv_of_joint
#print axioms MeasureEquivalenceSharedDensity.invariantConditionalKernel_shared_rnDeriv
