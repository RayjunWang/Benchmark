import OperatorTargets
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The canonical Hilbert space has its actual norm Polish topology;
its coordinate map is a measurable embedding for this topology. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace OperatorCoding

noncomputable section

def hilbertFiniteTruncation (s : Finset ℕ) (x : ℕ → ℂ) : CanonicalHilbert :=
  ∑ i ∈ s, lp.single 2 i (x i)

theorem hilbertFiniteTruncation_continuous (s : Finset ℕ) :
    Continuous (hilbertFiniteTruncation s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℂ) 2 i).continuous.comp
    (continuous_apply i)

instance canonicalHilbert_separable : SeparableSpace CanonicalHilbert := by
  have hd : Dense (⋃ s : Finset ℕ, Set.range (hilbertFiniteTruncation s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
    exact Filter.Eventually.of_forall (fun s => Set.mem_iUnion.mpr ⟨s, ⟨(x:ℕ→ℂ), rfl⟩⟩)
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (hilbertFiniteTruncation_continuous s))

instance canonicalHilbert_polish : PolishSpace CanonicalHilbert := inferInstance

example : SecondCountableTopology CanonicalHilbert := inferInstance

theorem canonicalHilbert_coordinates_continuous :
    Continuous (fun x : CanonicalHilbert => (x : ℕ → ℂ)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℂ) 2 i).continuous

theorem canonicalHilbert_coordinates_measurableEmbedding :
    @MeasurableEmbedding CanonicalHilbert (ℕ → ℂ) (borel CanonicalHilbert)
      inferInstance (fun x => (x : ℕ → ℂ)) := by
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  exact canonicalHilbert_coordinates_continuous.measurableEmbedding (fun _ _ h => lp.ext h)

end
end OperatorCoding

#print axioms OperatorCoding.canonicalHilbert_coordinates_measurableEmbedding
