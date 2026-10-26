import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.LpOrder

/-!
Actual measure identification from nonnegative L1 density approximations.
The hypotheses concern a generating pi-system; the conclusion is equality
of measures, followed by absolute continuity. No Gaussian identities or
product-affinity computations are assumed to have been formalized here.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureEquivalenceDensityExtension

variable {α : Type*} [m : MeasurableSpace α]
  {μ ν : Measure α} [IsFiniteMeasure ν]

theorem measure_eq_withDensity_of_L1_approx
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hpos : ∀ n, 0 ≤ f n)
    (hlim : Tendsto f atTop (𝓝 g))
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, f n x ∂μ) = ν s) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
  have hgpos : g ∈ Set.Ici (0 : Lp ℝ 1 μ) :=
    isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall hpos)
  have hg_ae : 0 ≤ᵐ[μ] g := (Lp.coeFn_nonneg g).mpr hgpos
  have hvals : ∀ s ∈ C,
      ENNReal.ofReal (∫ x in s, g x ∂μ) = ν s := by
    intro s hs
    apply tendsto_nhds_unique
      ((ENNReal.continuous_ofReal.comp (continuous_setIntegral s)).tendsto g |>.comp hlim)
    exact tendsto_const_nhds.congr' (by
      filter_upwards [hmatch s hs] with n hn
      exact hn.symm)
  have hmeas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hs
  have hwd : ∀ s ∈ C,
      μ.withDensity (fun x => ENNReal.ofReal (g x)) s = ν s := by
    intro s hs
    rw [withDensity_apply _ (hmeas s hs),
      ← ofReal_integral_eq_lintegral_ofReal
        (L1.integrable_coeFn g).restrict (ae_restrict_of_ae hg_ae)]
    exact hvals s hs
  exact ext_of_generate_finite C hgen hpi
    (fun s hs => (hwd s hs).symm) (hwd Set.univ huniv).symm

theorem absolutelyContinuous_of_L1_approx
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hpos : ∀ n, 0 ≤ f n)
    (hlim : Tendsto f atTop (𝓝 g))
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, f n x ∂μ) = ν s) :
    ν ≪ μ := by
  rw [measure_eq_withDensity_of_L1_approx C hgen hpi huniv f g hpos hlim hmatch]
  exact withDensity_absolutelyContinuous _ _

theorem product_measure_eq_withDensity_of_L1_cylinder_approx
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ ν : Measure (∀ i, X i)} [IsFiniteMeasure ν]
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hpos : ∀ n, 0 ≤ f n)
    (hlim : Tendsto f atTop (𝓝 g))
    (hmatch : ∀ (I : Finset ι) (s : Set (∀ i : I, X i)), MeasurableSet s →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (∫ x in cylinder I s, f n x ∂μ) = ν (cylinder I s)) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
  apply measure_eq_withDensity_of_L1_approx (measurableCylinders X)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders X) f g hpos hlim
  intro s hs
  obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  exact hmatch I t ht

end MeasureEquivalenceDensityExtension

#print axioms MeasureEquivalenceDensityExtension.measure_eq_withDensity_of_L1_approx
#print axioms MeasureEquivalenceDensityExtension.absolutelyContinuous_of_L1_approx
#print axioms MeasureEquivalenceDensityExtension.product_measure_eq_withDensity_of_L1_cylinder_approx
