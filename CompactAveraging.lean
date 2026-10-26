import KernelEquivalence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Topology.Algebra.MulAction

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceCompactAveraging

/-!
`ProbabilityMeasure Y` carries mathlib's canonical evaluation/Giry measurable
structure. A measurable probability-valued map therefore supplies an actual
Markov kernel without any extra kernel hypothesis. The Haar normalization,
joint probability, and exact translation quasi-invariance are constructed
below, including the concrete compact torus and a continuous action adapter.
-/

open MeasureEquivalenceResearch

section Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def probabilityKernel (f : X → ProbabilityMeasure Y) (hf : Measurable f) : Kernel X Y where
  toFun x := (f x : Measure Y)
  measurable' := measurable_subtype_coe.comp hf

@[simp] lemma probabilityKernel_apply (f : X → ProbabilityMeasure Y) (hf : Measurable f)
    (x : X) : probabilityKernel f hf x = (f x : Measure Y) := rfl

instance probabilityKernel_markov (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    IsMarkovKernel (probabilityKernel f hf) where
  isProbabilityMeasure x := (f x).property

def averagedMeasure (μ : Measure X) (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    Measure (X × Y) := μ ⊗ₘ probabilityKernel f hf

instance averagedMeasure_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    IsProbabilityMeasure (averagedMeasure μ f hf) := by
  unfold averagedMeasure
  infer_instance

lemma averagedMeasure_apply_prod (μ : Measure X) [SFinite μ]
    (f : X → ProbabilityMeasure Y) (hf : Measurable f)
    {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    averagedMeasure μ f hf (s ×ˢ t) = ∫⁻ x in s, (f x : Measure Y) t ∂μ := by
  exact Measure.compProd_apply_prod hs ht

end Kernel

section CompactGroup

variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the actual compact whole group. -/
def compactHaar : Measure G := Measure.addHaarMeasure (⊤ : PositiveCompacts G)

instance compactHaar_probability : IsProbabilityMeasure (compactHaar G) := by
  constructor
  simpa [compactHaar] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))

instance compactHaar_invariant : Measure.IsAddLeftInvariant (compactHaar G) := by
  unfold compactHaar
  infer_instance

variable {G} {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]

theorem exact_quasi_invariance_of_probability_reduction
    (H : AddSubgroup G) (f : G → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H)
    (g : G) :
    EquivalentMeasures
      ((averagedMeasure (compactHaar G) f hf).map (fun z => (g + z.1, z.2)))
      (averagedMeasure (compactHaar G) f hf) ↔ g ∈ H := by
  exact exact_quasi_invariance_of_kernel_reduction (compactHaar G) H
    (probabilityKernel f hf) hred g

end CompactGroup

section Action

/-- The multiplicative-tag action used to feed the additive averaging measure to RNGraph. -/
abbrev baseTranslationAction (G Y : Type*) [AddMonoid G] :
    MulAction (Multiplicative G) (G × Y) where
  smul g z := (g.toAdd + z.1, z.2)
  one_smul z := by
    change (0 + z.1, z.2) = z
    simp
  mul_smul g h z := by
    change (g.toAdd + h.toAdd + z.1, z.2) = (g.toAdd + (h.toAdd + z.1), z.2)
    rw [add_assoc]

theorem continuous_baseTranslationAction (G Y : Type*)
    [AddMonoid G] [TopologicalSpace G] [ContinuousAdd G] [TopologicalSpace Y] :
    letI := baseTranslationAction G Y
    ContinuousSMul (Multiplicative G) (G × Y) := by
  let _ := baseTranslationAction G Y
  constructor
  change Continuous (fun z : Multiplicative G × (G × Y) =>
    (z.1.toAdd + z.2.1, z.2.2))
  exact ((continuous_toAdd.comp continuous_fst).add
    (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)

theorem exact_quasi_invariance_action
    {G Y : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (H : AddSubgroup G) (f : G → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    letI := baseTranslationAction G Y
    ∀ g : Multiplicative G,
      EquivalentMeasures ((averagedMeasure (compactHaar G) f hf).map (fun z => g • z))
        (averagedMeasure (compactHaar G) f hf) ↔ g.toAdd ∈ H := by
  intro g
  exact exact_quasi_invariance_of_probability_reduction H f hf hred g.toAdd

end Action

abbrev Torus := ℕ → UnitAddCircle

example : CompactSpace Torus := inferInstance
example : MeasurableSpace Torus := inferInstance
example : BorelSpace Torus := inferInstance
example : PolishSpace Torus := inferInstance

theorem torus_averaging
    {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    (H : AddSubgroup Torus) (f : Torus → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    ∃ M : Measure (Torus × Y), IsProbabilityMeasure M ∧
      ∀ g : Torus, EquivalentMeasures (M.map (fun z => (g + z.1, z.2))) M ↔ g ∈ H := by
  exact ⟨averagedMeasure (compactHaar Torus) f hf, inferInstance,
    exact_quasi_invariance_of_probability_reduction H f hf hred⟩

/-- Actual Polish sample-space version with the RNGraph-compatible action. -/
theorem torus_polish_action_averaging
    {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (H : AddSubgroup Torus) (f : Torus → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    letI := baseTranslationAction Torus Y
    ∃ M : Measure (Torus × Y), IsProbabilityMeasure M ∧
      ∀ g : Multiplicative Torus,
        (M.map (fun z => g • z) ≪ M ∧ M ≪ M.map (fun z => g • z)) ↔ g.toAdd ∈ H := by
  exact ⟨averagedMeasure (compactHaar Torus) f hf, inferInstance,
    exact_quasi_invariance_action H f hf hred⟩

#print axioms probabilityKernel_markov
#print axioms compactHaar_probability
#print axioms exact_quasi_invariance_of_probability_reduction
#print axioms torus_averaging
#print axioms continuous_baseTranslationAction
#print axioms torus_polish_action_averaging

end MeasureEquivalenceCompactAveraging
