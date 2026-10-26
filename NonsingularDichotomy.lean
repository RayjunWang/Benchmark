import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
The equivalence-or-singularity dichotomy for ergodic nonsingular measures
of one countable group action. Ergodicity is stated explicitly for
measurable invariant sets; no invariance of the measures is assumed.
-/

open MeasureTheory MeasureTheory.Measure Set

namespace MeasureEquivalenceRigidity

variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]

/-- The union of all inverse translates of a set. -/
def orbitSaturation (s : Set Y) : Set Y :=
  ⋃ g : G, (fun y => g • y) ⁻¹' s

omit [Countable G] [MeasurableSpace Y] in
theorem subset_orbitSaturation (s : Set Y) : s ⊆ orbitSaturation (G := G) s := by
  intro y hy
  exact mem_iUnion.mpr ⟨1, by simpa using hy⟩

omit [Countable G] [MeasurableSpace Y] in
theorem preimage_orbitSaturation (s : Set Y) (h : G) :
    (fun y => h • y) ⁻¹' orbitSaturation (G := G) s = orbitSaturation (G := G) s := by
  ext y
  constructor
  · intro hy
    rcases mem_iUnion.mp hy with ⟨g, hg⟩
    exact mem_iUnion.mpr ⟨g * h, by simpa [mul_smul] using hg⟩
  · intro hy
    rcases mem_iUnion.mp hy with ⟨g, hg⟩
    exact mem_iUnion.mpr ⟨g * h⁻¹, by simpa [mul_smul] using hg⟩

/-- An ergodic measure is either absolutely continuous with respect to
a nonsingular measure for the same countable action, or singular to it.
Ergodicity here requires only the usual null-or-conull invariant-set test. -/
theorem absolutelyContinuous_or_mutuallySingular_of_ergodic
    (μ ν : Measure Y)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0) :
    μ ≪ ν ∨ μ ⟂ₘ ν := by
  classical
  by_cases hμν : μ ≪ ν
  · exact Or.inl hμν
  right
  change ¬ (∀ ⦃s : Set Y⦄, ν s = 0 → μ s = 0) at hμν
  push Not at hμν
  obtain ⟨s, hνs, hμs⟩ := hμν
  let t := toMeasurable ν s
  have htm : MeasurableSet t := measurableSet_toMeasurable _ _
  have hνt : ν t = 0 := (measure_toMeasurable s).trans hνs
  have hμt : μ t ≠ 0 := fun h => hμs (measure_mono_null (subset_toMeasurable _ _) h)
  have hSatMeas : MeasurableSet (orbitSaturation (G := G) t) := by
    exact MeasurableSet.iUnion (fun g => htm.preimage (hνns g).measurable)
  have hνSat : ν (orbitSaturation (G := G) t) = 0 := by
    apply measure_iUnion_null
    intro g
    exact (hνns g).preimage_null hνt
  have hμSat : μ (orbitSaturation (G := G) t) ≠ 0 := by
    intro h
    exact hμt (measure_mono_null (subset_orbitSaturation t) h)
  have hμSatc : μ (orbitSaturation (G := G) t)ᶜ = 0 :=
    (hμerg _ hSatMeas (preimage_orbitSaturation t)).resolve_left hμSat
  exact ⟨(orbitSaturation (G := G) t)ᶜ, hSatMeas.compl, hμSatc, by simpa using hνSat⟩

/-- Two ergodic nonsingular measures for the same countable action
are equivalent or mutually singular. The ergodicity tests refer to
actual measurable invariant sets. The measures need not be invariant,
finite, or have the same Radon--Nikodym cocycle. -/
theorem equivalent_or_mutuallySingular_of_nonsingular_ergodic
    (μ ν : Measure Y)
    (hμns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) μ μ)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (hνerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → ν s = 0 ∨ ν sᶜ = 0) :
    (μ ≪ ν ∧ ν ≪ μ) ∨ μ ⟂ₘ ν := by
  rcases absolutelyContinuous_or_mutuallySingular_of_ergodic μ ν hνns hμerg with h | h
  · rcases absolutelyContinuous_or_mutuallySingular_of_ergodic ν μ hμns hνerg with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr h'.symm
  · exact Or.inr h

end MeasureEquivalenceRigidity

#print axioms MeasureEquivalenceRigidity.absolutelyContinuous_or_mutuallySingular_of_ergodic
#print axioms MeasureEquivalenceRigidity.equivalent_or_mutuallySingular_of_nonsingular_ergodic
