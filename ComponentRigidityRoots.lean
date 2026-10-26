import ComponentQuasiInvariance
import ErgodicComponents
import RigidityRoots
import HellingerKernel

/-! Actual component quasi-invariance is detected by Hellinger affinity,
and vanishing mean deficits along roots give component quasi-invariance. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceHellinger MeasureEquivalenceErgodicDecomposition

section Pointwise

variable {K G Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

/-- The zero-affinity test uses actual nonsingularity and ergodicity of
the conditional probability and actual commutation of the translate. -/
theorem component_affinity_zero_iff
    (y : Y) (k : K)
    (hns : ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) (κ y) (κ y))
    (herg : ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' B = B) → (κ y) B = 0 ∨ (κ y) Bᶜ = 0)
    (hcomm : ∀ (g : G) (z : Z), k • (g • z) = g • (k • z)) :
    affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y := by
  let e : Z ≃ᵐ Z := MeasurableEquiv.smul k
  letI : IsProbabilityMeasure ((κ y).map e) :=
    (κ y).isProbabilityMeasure_map e.measurable.aemeasurable
  have hecomm : ∀ (g : G) (z : Z), e (g • z) = g • e z := hcomm
  have hA := affinity_eq_zero_iff_not_equivalent_of_nonsingular_ergodic
    (κ y) ((κ y).map e) hns
    (nonsingular_map_of_commute (κ y) e hecomm hns) herg
    (ergodic_map_of_commute (κ y) e hecomm herg)
  simpa only [mem_componentQI_iff, and_comm] using hA

end Pointwise

section ActualComponents

variable {K G Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hns : ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns in
/-- One conull set of actual invariant conditional probabilities works
for every commuting translate. No uncountable intersection is taken. -/
theorem invariant_components_affinity_zero_iff :
    ∀ᵐ x ∂μ, ∀ k : K,
      (∀ (g : G) (z : Z), k • (g • z) = g • (k • z)) →
      (affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map (fun z => k • z)) = 0 ↔
          k ∉ componentQI (invariantConditionalKernel (G := G) μ) x) := by
  have hNS := invariantConditionalKernel_nonsingular_all μ hns
  have hErg := invariantConditionalKernel_ergodic μ hns
  filter_upwards [hNS, hErg] with x hxNS hxErg
  intro k hcomm
  exact component_affinity_zero_iff _ x k hxNS hxErg hcomm

end ActualComponents

section Roots

/-- A uniform lower estimate at zero and the probability upper bound
give convergence to one along the concrete real roots. -/
theorem tendsto_mean_along_real_roots
    (F : ℝ → ℝ) (hFle : ∀ b, F b ≤ 1)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ F b) (a : ℝ) :
    Tendsto (fun n : ℕ => F (a / ((n+1 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hroot : Tendsto (fun n : ℕ => a / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨δ, hδ, hbound⟩ := hsmall ((1-b)/2) (by linarith)
    have he : ∀ᶠ n : ℕ in atTop, |a / ((n+1 : ℕ) : ℝ)| < δ :=
      (tendsto_order.1 hroot.abs).2 δ (by simpa using hδ)
    filter_upwards [he] with n hn
    have := hbound _ hn
    linarith
  · intro b hb
    exact Eventually.of_forall (fun n => lt_of_le_of_lt (hFle _) hb)

variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (η : Measure Y) [IsProbabilityMeasure η]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

/-- Root divisibility, the actual zero-affinity test on the components,
and vanishing mean deficits imply actual component quasi-invariance.
The analytic mean estimate is the sole quantitative input. -/
theorem ae_componentQI_of_real_root_mean_affinity
    (g : ℝ →+ Additive K) (a : ℝ)
    (hzero : ∀ᵐ y ∂η, ∀ k : K,
      affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y,
      affinity (κ y) ((κ y).map (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z)) ∂η)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂η, Additive.toMul (g a) ∈ componentQI κ y := by
  let S : Y → AddSubgroup (Additive K) := fun y => (componentQI κ y).toAddSubgroup
  let A : ℕ → Y → ℝ := fun n y => affinity (κ y)
    ((κ y).map (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z))
  have hbad : ∀ n, MeasurableSet {y | g (a / ((n+1 : ℕ) : ℝ)) ∉ S y} := by
    intro n
    exact (measurableSet_componentQI κ _).compl
  have hAm : ∀ n, Measurable (A n) := by
    intro n
    simpa only [A, Kernel.map_apply _ (measurable_const_smul _)] using
      kernelAffinity_measurable κ
        (κ.map (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z))
  have hAzero : ∀ n, ∀ᵐ y ∂η, g (a / ((n+1 : ℕ) : ℝ)) ∉ S y → A n y = 0 := by
    intro n
    filter_upwards [hzero] with y hy
    intro hnot
    exact (hy _).mpr hnot
  have hAle : ∀ n y, A n y ≤ 1 := by
    intro n y
    letI : IsProbabilityMeasure ((κ y).map
        (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z)) :=
      (κ y).isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
    exact affinity_le_one _ _
  exact ae_mem_of_real_root_mean_affinity g S a A hbad hAm
    (fun n y => affinity_nonneg _ _) hAle hAzero ε hmean hε

/-- The epsilon-delta estimate supplied by compact upper semicontinuity
and the two-point approximation suffices for the actual roots argument. -/
theorem ae_componentQI_of_uniform_mean_affinity
    (g : ℝ →+ Additive K)
    (hzero : ∀ᵐ y ∂η, ∀ k : K,
      affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ ∫ y,
        affinity (κ y) ((κ y).map (fun z => Additive.toMul (g b) • z)) ∂η)
    (a : ℝ) :
    ∀ᵐ y ∂η, Additive.toMul (g a) ∈ componentQI κ y := by
  let F : ℝ → ℝ := fun b => ∫ y,
    affinity (κ y) ((κ y).map (fun z => Additive.toMul (g b) • z)) ∂η
  have hFle : ∀ b, F b ≤ 1 := by
    intro b
    have hle : ∀ y, affinity (κ y)
        ((κ y).map (fun z => Additive.toMul (g b) • z)) ≤ 1 := by
      intro y
      letI : IsProbabilityMeasure ((κ y).map (fun z => Additive.toMul (g b) • z)) :=
        (κ y).isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
      exact affinity_le_one _ _
    have hm : Measurable (fun y => affinity (κ y)
        ((κ y).map (fun z => Additive.toMul (g b) • z))) := by
      simpa only [Kernel.map_apply _ (measurable_const_smul _)] using
        kernelAffinity_measurable κ (κ.map (fun z => Additive.toMul (g b) • z))
    have hi : Integrable (fun y => affinity (κ y)
        ((κ y).map (fun z => Additive.toMul (g b) • z))) η :=
      Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
        (Eventually.of_forall (fun y => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (affinity_nonneg _ _)] using hle y))
    simpa only [F, integral_const, probReal_univ, one_smul] using
      integral_mono_ae hi (integrable_const (1 : ℝ)) (Eventually.of_forall hle)
  have hlim := tendsto_mean_along_real_roots F hFle hsmall a
  apply ae_componentQI_of_real_root_mean_affinity η κ g a hzero
    (fun n => 1 - F (a / ((n+1 : ℕ) : ℝ)))
  · intro n
    change 1 - (1 - F _) ≤ F _
    linarith
  · simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hlim

omit [IsProbabilityMeasure η] in
/-- Fiberwise equivalence passes through the actual barycenter. -/
theorem quasiInvariant_barycenter_of_ae_componentQI
    (k : K) (hQI : ∀ᵐ y ∂η, k ∈ componentQI κ y) :
    k ∈ MeasureEquivalenceRNGraph.quasiInvariantSubgroup (κ ∘ₘ η) := by
  rw [MeasureEquivalenceRNGraph.mem_quasiInvariantSubgroup_iff,
    Measure.map_comp η κ (measurable_const_smul k)]
  constructor
  · exact Measure.AbsolutelyContinuous.comp_left η (hQI.mono (fun y hy => by
      simpa only [Kernel.map_apply _ (measurable_const_smul k)] using
        (mem_componentQI_iff κ k y).mp hy |>.1))
  · exact Measure.AbsolutelyContinuous.comp_left η (hQI.mono (fun y hy => by
      simpa only [Kernel.map_apply _ (measurable_const_smul k)] using
        (mem_componentQI_iff κ k y).mp hy |>.2))

end Roots

section ActualRigidity

variable {K G Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hns : ∀ d : G, QuasiMeasurePreserving (fun z : Z => d • z) μ μ)

include hns in
/-- Full roots-and-barycenter conclusion for the actual invariant
conditional kernel. Ergodicity and nonsingularity of the components
are proved internally, rather than assumed as a disintegration axiom. -/
theorem quasiInvariant_of_uniform_invariant_mean_affinity
    (g : ℝ →+ Additive K)
    (hcomm : ∀ (k : K) (d : G) (z : Z), k • (d • z) = d • (k • z))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ ∫ x,
        affinity (invariantConditionalKernel (G := G) μ x)
          ((invariantConditionalKernel (G := G) μ x).map
            (fun z => Additive.toMul (g b) • z)) ∂μ)
    (a : ℝ) :
    Additive.toMul (g a) ∈ MeasureEquivalenceRNGraph.quasiInvariantSubgroup μ := by
  have hzero : ∀ᵐ x ∂μ, ∀ k : K,
      affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map (fun z => k • z)) = 0 ↔
          k ∉ componentQI (invariantConditionalKernel (G := G) μ) x := by
    filter_upwards [invariant_components_affinity_zero_iff (K := K) μ hns] with x hx
    exact fun k => hx k (hcomm k)
  have hQI := ae_componentQI_of_uniform_mean_affinity μ
    (invariantConditionalKernel (G := G) μ) g hzero hsmall a
  have h := quasiInvariant_barycenter_of_ae_componentQI μ
    (invariantConditionalKernel (G := G) μ) (Additive.toMul (g a)) hQI
  rwa [invariantConditionalKernel_comp] at h

end ActualRigidity

end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.component_affinity_zero_iff
#print axioms MeasureEquivalenceRigidity.invariant_components_affinity_zero_iff
#print axioms MeasureEquivalenceRigidity.ae_componentQI_of_real_root_mean_affinity
#print axioms MeasureEquivalenceRigidity.tendsto_mean_along_real_roots
#print axioms MeasureEquivalenceRigidity.ae_componentQI_of_uniform_mean_affinity
#print axioms MeasureEquivalenceRigidity.quasiInvariant_barycenter_of_ae_componentQI
#print axioms MeasureEquivalenceRigidity.quasiInvariant_of_uniform_invariant_mean_affinity
