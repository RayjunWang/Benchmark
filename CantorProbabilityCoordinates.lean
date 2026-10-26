import CantorHaarCylinders
import MeasureCantorTuple
import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureUnitary

theorem isClopen_cantorCylinder (k : CantorCylinderIndex) : IsClopen (cantorCylinder k) := by
  change IsClopen ((fun x : HaarCantor => fun i : k.1 => x i) ⁻¹' k.2)
  exact (isClopen_discrete k.2).preimage (continuous_pi fun i => continuous_apply (i : ℕ))

def cantorProbabilityCoordinates (μ : ProbabilityMeasure HaarCantor) : CantorCylinderIndex → ℝ :=
  fun k => (μ : Measure HaarCantor).real (cantorCylinder k)

theorem continuous_cantorProbabilityCoordinates : Continuous cantorProbabilityCoordinates :=
  continuous_pi (fun k => continuous_clopen_mass _ (isClopen_cantorCylinder k))

theorem injective_cantorProbabilityCoordinates : Function.Injective cantorProbabilityCoordinates := by
  intro μ ν h
  apply Subtype.ext
  change (μ : Measure HaarCantor) = (ν : Measure HaarCantor)
  apply ext_of_generate_finite (range cantorCylinder) cantorCylinder_generates.symm cantorCylinder_isPiSystem
  · rintro s ⟨k,rfl⟩
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ : Measure HaarCantor) _)
      (measure_ne_top (ν : Measure HaarCantor) _)).mp
    exact congrFun h k
  · simp

theorem isEmbedding_cantorProbabilityCoordinates : IsEmbedding cantorProbabilityCoordinates :=
  continuous_cantorProbabilityCoordinates.isClosedEmbedding injective_cantorProbabilityCoordinates |>.isEmbedding

/-- The weak topology on Cantor probabilities is exactly the topology of all finite-cylinder masses. -/
theorem continuous_cantorProbability_iff {X : Type*} [TopologicalSpace X]
    (f : X → ProbabilityMeasure HaarCantor) :
    Continuous f ↔ ∀ k : CantorCylinderIndex,
      Continuous (fun x => (f x : Measure HaarCantor).real (cantorCylinder k)) := by
  rw [isEmbedding_cantorProbabilityCoordinates.continuous_iff, continuous_pi_iff]
  rfl

theorem tendsto_cantorProbability_iff {I : Type*} {L : Filter I}
    (f : I → ProbabilityMeasure HaarCantor) (μ : ProbabilityMeasure HaarCantor) :
    Tendsto f L (𝓝 μ) ↔ ∀ k : CantorCylinderIndex,
      Tendsto (fun i => (f i : Measure HaarCantor).real (cantorCylinder k)) L
        (𝓝 ((μ : Measure HaarCantor).real (cantorCylinder k))) := by
  rw [isEmbedding_cantorProbabilityCoordinates.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

theorem cantorProbability_finite_coordinate_neighborhood (μ : ProbabilityMeasure HaarCantor)
    {U : Set (ProbabilityMeasure HaarCantor)} (hU : U ∈ 𝓝 μ) :
    ∃ (I : Finset CantorCylinderIndex) (V : CantorCylinderIndex → Set ℝ),
      (∀ k, V k ∈ 𝓝 (cantorProbabilityCoordinates μ k)) ∧
      ∀ ν : ProbabilityMeasure HaarCantor,
        (∀ k ∈ I, cantorProbabilityCoordinates ν k ∈ V k) → ν ∈ U := by
  classical
  rw [isEmbedding_cantorProbabilityCoordinates.isInducing.nhds_eq_comap μ] at hU
  obtain ⟨W,hW,hWU⟩ := Filter.mem_comap.mp hU
  rw [nhds_pi,Filter.mem_pi'] at hW
  obtain ⟨I,V,hV,hVW⟩ := hW
  refine ⟨I,V,hV,fun ν hν => hWU (hVW ?_)⟩
  exact fun k hk => hν k hk

end BenchmarkJump

#print axioms BenchmarkJump.continuous_cantorProbability_iff
