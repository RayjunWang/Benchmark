import WeightedDominatingKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace SpectralDomination

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]

def kernelSupport (κ η : Kernel X Y) (x : X) : Set Y :=
  {y | κ.rnDeriv η x y ≠ 0}

theorem measurableSet_kernelSupport (κ η : Kernel X Y) (x : X) :
    MeasurableSet (kernelSupport κ η x) :=
  (Kernel.measurable_rnDeriv κ η).of_uncurry_left (measurableSet_singleton (0 : ℝ≥0∞)).compl

theorem measurableSet_kernelSupport_joint (κ η : Kernel X Y) :
    MeasurableSet {p : X × Y | p.2 ∈ kernelSupport κ η p.1} :=
  (Kernel.measurable_rnDeriv κ η) (measurableSet_singleton (0 : ℝ≥0∞)).compl

theorem kernel_support_equivalent (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (x : X) (hac : κ x ≪ η x) :
    κ x ≪ (η x).restrict (kernelSupport κ η x) ∧
      (η x).restrict (kernelSupport κ η x) ≪ κ x := by
  have he : (η x).withDensity (κ.rnDeriv η x) = κ x := by
    simpa only [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ η)] using
      (Kernel.withDensity_rnDeriv_eq (κ := κ) (η := η) hac)
  have hae : ae ((η x).withDensity (κ.rnDeriv η x)) =
      ae ((η x).restrict (kernelSupport κ η x)) := by
    apply Filter.ext
    intro s
    exact ae_withDensity_iff_ae_restrict (Kernel.measurable_rnDeriv κ η).of_uncurry_left
  rw [he] at hae
  exact ⟨Measure.ae_le_iff_absolutelyContinuous.mp hae.le,
    Measure.ae_le_iff_absolutelyContinuous.mp hae.ge⟩

def supportKernel (κ η : Kernel X Y) [IsFiniteKernel η] : Kernel X Y := by
  classical
  exact η.withDensity (fun x y => (kernelSupport κ η x).indicator (fun _ => 1) y)

theorem measurable_supportDensity (κ η : Kernel X Y) :
    Measurable (Function.uncurry (fun x y => (kernelSupport κ η x).indicator (fun _ => (1 : ℝ≥0∞)) y)) := by
  classical
  exact Measurable.ite (measurableSet_kernelSupport_joint κ η) measurable_const measurable_const

theorem supportKernel_apply (κ η : Kernel X Y) [IsFiniteKernel η] (x : X) :
    supportKernel κ η x = (η x).restrict (kernelSupport κ η x) := by
  rw [supportKernel, Kernel.withDensity_apply _ (measurable_supportDensity κ η)]
  exact withDensity_indicator_one (measurableSet_kernelSupport κ η x)

instance supportKernel_finite (κ η : Kernel X Y) [IsFiniteKernel η] :
    IsFiniteKernel (supportKernel κ η) := by
  classical
  unfold supportKernel
  apply Kernel.isFiniteKernel_withDensity_of_bounded η (B := 1) (by simp)
  intro x y
  simp only [Set.indicator_apply]
  split_ifs <;> simp

end SpectralDomination

#print axioms SpectralDomination.kernel_support_equivalent
