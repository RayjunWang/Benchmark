import SharedConditionalDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! The actual invariant conditional kernel is constant almost everywhere
on almost every conditional fiber. Countability is used only for a family
that determines finite measures, so no AE/uncountable-forall swap is made. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

theorem conditional_fiber_constant {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y]
    (f : InvariantBase G Z → Y) (hf : Measurable f) :
    ∀ᵐ x ∂μ, ∀ᵐ z ∂(invariantConditionalKernel (G := G) μ x),
      f (invariantBaseMap (G := G) z) = f (invariantBaseMap (G := G) x) := by
  let β := μ.map (invariantBaseMap (G := G))
  let κ := invariantBaseKernel (G := G) μ
  have hj : (fun p : InvariantBase G Z × Z => f p.1) =ᵐ[β ⊗ₘ κ]
      (fun p => f (invariantBaseMap (G := G) p.2)) := by
    apply Filter.EventuallyEq.of_forall_separating_mem_iff MeasurableSet
    intro U hU
    have hp : MeasurableSet {p : InvariantBase G Z × Z |
        f p.1 ∈ U ↔ f (invariantBaseMap (G := G) p.2) ∈ U} :=
      (hU.preimage (hf.comp measurable_fst)).iff
        (hU.preimage (hf.comp ((invariantBaseMap_measurable (G := G)).comp measurable_snd)))
    change ∀ᵐ p ∂(μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ,
      f p.1 ∈ U ↔ f (invariantBaseMap (G := G) p.2) ∈ U
    rw [invariantBaseKernel_joint]
    rw [ae_iff]
    change (μ.map (fun z => (invariantBaseMap (G := G) z,z)))
      ({p : InvariantBase G Z × Z | f p.1 ∈ U ↔ f (invariantBaseMap (G := G) p.2) ∈ U}ᶜ) = 0
    have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z,z)) :=
      (invariantBaseMap_measurable (G := G)).prodMk measurable_id
    rw [Measure.map_apply (μ := μ) hgraph hp.compl]
    change μ {z | ¬ (f (invariantBaseMap (G := G) z) ∈ U ↔
      f (invariantBaseMap (G := G) z) ∈ U)} = 0
    simp
  have h := Measure.ae_ae_of_ae_compProd hj.symm
  exact ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable h

def determiningSet (s : Finset ℕ) : Set Z :=
  ⋂ i ∈ s, MeasurableSpace.natGeneratingSequence Z i

theorem determiningSet_measurable (s : Finset ℕ) : MeasurableSet (determiningSet (Z := Z) s) :=
  s.measurableSet_biInter (fun i _hi => MeasurableSpace.measurableSet_natGeneratingSequence (α := Z) i)

theorem determiningSet_isPiSystem : IsPiSystem (range (determiningSet (Z := Z))) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _hne
  refine ⟨s ∪ t, ?_⟩
  ext z
  simp [determiningSet, Finset.mem_union, or_imp, forall_and]

theorem determiningSet_generates :
    MeasurableSpace.generateFrom (range (determiningSet (Z := Z))) = ‹MeasurableSpace Z› := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro B hB
    rcases hB with ⟨s, rfl⟩
    exact determiningSet_measurable s
  · have hs : range (MeasurableSpace.natGeneratingSequence Z) ⊆
        range (determiningSet (Z := Z)) := by
      rintro _ ⟨n, rfl⟩
      exact ⟨{n}, by ext z; simp [determiningSet]⟩
    exact (MeasurableSpace.generateFrom_natGeneratingSequence (α := Z)).symm.le.trans
      (MeasurableSpace.generateFrom_mono hs)

def invariantKernelCode (x : InvariantBase G Z) (s : Finset ℕ) : ℝ≥0∞ :=
  invariantBaseKernel (G := G) μ x (determiningSet s)

theorem invariantKernelCode_measurable : Measurable (invariantKernelCode (G := G) μ) := by
  apply measurable_pi_iff.mpr
  intro s
  exact (invariantBaseKernel (G := G) μ).measurable_coe (determiningSet_measurable s)

/-- A single conull family of actual conditional probabilities, each
concentrated on points with the same conditional probability. -/
theorem invariantConditionalKernel_fibers_constant :
    ∀ᵐ x ∂μ, ∀ᵐ z ∂(invariantConditionalKernel (G := G) μ x),
      invariantConditionalKernel (G := G) μ z = invariantConditionalKernel (G := G) μ x := by
  have h := conditional_fiber_constant μ (invariantKernelCode (G := G) μ)
    (invariantKernelCode_measurable (G := G) μ)
  filter_upwards [h] with x hx
  filter_upwards [hx] with z hz
  apply MeasureTheory.ext_of_generate_finite (range (determiningSet (Z := Z)))
    determiningSet_generates.symm determiningSet_isPiSystem
  · rintro _ ⟨s, rfl⟩
    exact congrFun hz s
  · simp

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.conditional_fiber_constant
#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_fibers_constant
