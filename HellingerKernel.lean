import HellingerAffinity
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual disintegration of Hellinger affinity for equal-marginal kernels. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]

theorem joint_rnDeriv_of_kernel_ac (hac : ∀ x, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      (fun p => κ.rnDeriv η p.1 p.2) := by
  have hk : η.withDensity (κ.rnDeriv η) = κ := by
    ext x : 1
    exact Kernel.withDensity_rnDeriv_eq (hac x)
  have hD : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    rw [← Measure.compProd_withDensity (κ.measurable_rnDeriv η), hk]
  have h := (μ ⊗ₘ η).rnDeriv_withDensity (κ.measurable_rnDeriv η)
  rw [← hD] at h
  exact h

/-- The same density identity requires fiberwise absolute continuity only
almost everywhere under the common marginal. -/
theorem joint_rnDeriv_of_kernel_ac_ae (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      (fun p => κ.rnDeriv η p.1 p.2) := by
  have hk : η.withDensity (κ.rnDeriv η) =ᵐ[μ] κ :=
    hac.mono (fun _ h => Kernel.withDensity_rnDeriv_eq h)
  have hD : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    rw [← Measure.compProd_withDensity (κ.measurable_rnDeriv η)]
    exact Measure.compProd_congr hk.symm
  have h := (μ ⊗ₘ η).rnDeriv_withDensity (κ.measurable_rnDeriv η)
  rw [← hD] at h
  exact h

noncomputable def kernelAffinityIntegrand (p : X × Y) : ℝ :=
  Real.sqrt (κ.rnDeriv (κ+η) p.1 p.2).toReal *
    Real.sqrt (η.rnDeriv (κ+η) p.1 p.2).toReal

theorem kernelAffinityIntegrand_measurable : Measurable (kernelAffinityIntegrand κ η) :=
  (κ.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt.mul
    (η.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt

theorem affinity_kernel_fiber (x : X) :
    (∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) = affinity (κ x) (η x) := by
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x),
    η.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x)] with y hk he
  simp only [kernelAffinityIntegrand, hk, he]
  rfl

theorem kernelAffinity_measurable : Measurable (fun x => affinity (κ x) (η x)) := by
  have h := (kernelAffinityIntegrand_measurable κ η).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ+η)
  have he : (fun x => ∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) =
      fun x => affinity (κ x) (η x) := funext (affinity_kernel_fiber κ η)
  rw [he] at h
  exact h.measurable

theorem affinity_compProd :
    affinity (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫ x, affinity (κ x) (η x) ∂μ := by
  have hk : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ (κ+η)) =ᵐ[μ ⊗ₘ (κ+η)]
      fun p => κ.rnDeriv (κ+η) p.1 p.2 :=
    joint_rnDeriv_of_kernel_ac μ κ (κ+η)
      (fun x => Measure.AbsolutelyContinuous.rfl.add_right (η x))
  have he : (μ ⊗ₘ η).rnDeriv (μ ⊗ₘ (κ+η)) =ᵐ[μ ⊗ₘ (κ+η)]
      fun p => η.rnDeriv (κ+η) p.1 p.2 :=
    joint_rnDeriv_of_kernel_ac μ η (κ+η)
      (fun x => Measure.AbsolutelyContinuous.rfl.add_right' (κ x))
  have hf : (fun p => Real.sqrt ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ (κ+η)) p).toReal *
      Real.sqrt ((μ ⊗ₘ η).rnDeriv (μ ⊗ₘ (κ+η)) p).toReal) =ᵐ[μ ⊗ₘ (κ+η)]
        kernelAffinityIntegrand κ η := by
    filter_upwards [hk, he] with p hkp hep
    simp only [kernelAffinityIntegrand, hkp, hep]
  have hI : Integrable (kernelAffinityIntegrand κ η) (μ ⊗ₘ (κ+η)) := by
    have h := integrable_affinity_integrand (μ ⊗ₘ κ) (μ ⊗ₘ η)
    rw [← Measure.compProd_add_right] at h
    exact h.congr hf
  calc
    affinity (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫ p, kernelAffinityIntegrand κ η p ∂(μ ⊗ₘ (κ+η)) := by
      rw [affinity_integral, ← Measure.compProd_add_right]
      exact integral_congr_ae hf
    _ = ∫ x, ∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x) ∂μ :=
      Measure.integral_compProd hI
    _ = _ := integral_congr_ae (Eventually.of_forall (affinity_kernel_fiber κ η))

end MeasureEquivalenceHellinger

#print axioms MeasureEquivalenceHellinger.joint_rnDeriv_of_kernel_ac
#print axioms MeasureEquivalenceHellinger.kernelAffinity_measurable
#print axioms MeasureEquivalenceHellinger.affinity_compProd
