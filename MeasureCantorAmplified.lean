import MeasureCantorReflection
import OperatorTargets

/-! An infinite-multiplicity Cantor representation, on Hilbert-valued L².
The coefficient Hilbert space is fixed, but the measure-dependent L² spaces
are not yet identified with one canonical Hilbert space in a Borel fashion. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def vectorCantorMultiplier (μ : Measure CantorSpace) (k : CantorCylinderIndex) :
    Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ :=
  phaseEquiv μ (cantorCylinderPhase k) (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k)

def VectorCantorMultiplierEquivalent (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (μ ν : Measure CantorSpace) : Prop :=
  ∃ U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν,
    ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)

theorem equivalentMeasures_vectorCantorMultiplierEquivalent (μ ν : Measure CantorSpace)
    [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    VectorCantorMultiplierEquivalent E μ ν := by
  refine ⟨rnWeightedEquiv μ ν hμν hνμ, fun k f => ?_⟩
  exact rnWeightedEquiv_intertwines_phase μ (cantorCylinderPhase k)
    (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) ν hμν hνμ f

theorem indicatorL2_vectorCantorMultiplier (μ : Measure CantorSpace) (k : CantorCylinderIndex)
    (f : Lp E 2 μ) :
    indicatorL2 μ (cantorCylinder_measurable k) f =
      (1 / 2 : ℂ) • (f + vectorCantorMultiplier μ k f) := by
  change indicatorL2 μ (cantorCylinder_measurable k) f =
    (1 / 2 : ℂ) • (f + phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f)
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ (cantorCylinder_measurable k) f,
    Lp.coeFn_smul (1 / 2 : ℂ) (f + phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f),
    Lp.coeFn_add f (phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f),
    phaseMap_coe μ (cantorCylinderPhase k) (cantorCylinderPhase_measurable k)
      (cantorCylinderPhase_norm k) f] with x hI hs ha hp
  simp only [Pi.smul_apply, Pi.add_apply] at hs ha
  rw [hI, hs, ha, hp]
  classical
  by_cases hxs : x ∈ cantorCylinder k
  · simp only [cantorCylinderPhase, if_pos hxs, indicator_of_mem hxs, one_smul]
    rw [← two_smul ℂ (f x), smul_smul]
    norm_num
  · simp only [cantorCylinderPhase, if_neg hxs, indicator_of_notMem hxs, neg_one_smul,
      add_neg_cancel, smul_zero]

theorem vectorCantorMultiplier_intertwines_indicators (μ ν : Measure CantorSpace)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f))
    (k : CantorCylinderIndex) (f : Lp E 2 μ) :
    U (indicatorL2 μ (cantorCylinder_measurable k) f) =
      indicatorL2 ν (cantorCylinder_measurable k) (U f) := by
  rw [indicatorL2_vectorCantorMultiplier, U.map_smul, U.map_add, hU,
    ← indicatorL2_vectorCantorMultiplier]

theorem vectorCantorMultiplier_intertwiner_density (μ ν : Measure CantorSpace) [IsFiniteMeasure μ]
    (v : E) (hv : ‖v‖ = 1) (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)) :
    μ = vectorDensityMeasure ν (U (constantVectorL2 μ v)) := by
  have hmass : ∀ k : CantorCylinderIndex,
      μ (cantorCylinder k) = vectorDensityMeasure ν (U (constantVectorL2 μ v)) (cantorCylinder k) := by
    intro k
    calc
      μ (cantorCylinder k) = vectorDensityMeasure μ (constantVectorL2 μ v) (cantorCylinder k) := by
        rw [constantVectorL2_density μ v hv]
      _ = ENNReal.ofReal (‖indicatorL2 μ (cantorCylinder_measurable k) (constantVectorL2 μ v)‖ ^ 2) :=
        vectorDensityMeasure_apply _ _ _
      _ = ENNReal.ofReal (‖indicatorL2 ν (cantorCylinder_measurable k) (U (constantVectorL2 μ v))‖ ^ 2) := by
        rw [← vectorCantorMultiplier_intertwines_indicators μ ν U hU, U.norm_map]
      _ = vectorDensityMeasure ν (U (constantVectorL2 μ v)) (cantorCylinder k) :=
        (vectorDensityMeasure_apply _ _ _).symm
  apply ext_of_generate_finite (Set.range cantorCylinder) cantorCylinder_generates.symm
    cantorCylinder_isPiSystem
  · rintro s ⟨k, rfl⟩
    exact hmass k
  · have h := hmass (⟨∅, Set.univ⟩ : CantorCylinderIndex)
    simpa [cantorCylinder, cylinder] using h

theorem vectorCantorMultiplier_intertwiner_absolutelyContinuous (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] (v : E) (hv : ‖v‖ = 1) (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)) : μ ≪ ν := by
  rw [vectorCantorMultiplier_intertwiner_density μ ν v hv U hU]
  exact vectorDensityMeasure_absolutelyContinuous ν _

theorem vectorCantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : E) (hv : ‖v‖ = 1) :
    VectorCantorMultiplierEquivalent E μ ν ↔ μ ≪ ν ∧ ν ≪ μ := by
  constructor
  · rintro ⟨U, hU⟩
    constructor
    · exact vectorCantorMultiplier_intertwiner_absolutelyContinuous μ ν v hv U hU
    · apply vectorCantorMultiplier_intertwiner_absolutelyContinuous ν μ v hv U.symm
      intro k f
      apply U.injective
      simpa using (hU k (U.symm f)).symm
  · intro h
    exact equivalentMeasures_vectorCantorMultiplierEquivalent μ ν h.1 h.2

noncomputable def canonicalHilbertUnitVector : OperatorCoding.CanonicalHilbert :=
  lp.single 2 0 (1 : ℂ)

theorem canonicalHilbertUnitVector_norm : ‖canonicalHilbertUnitVector‖ = 1 := by
  change ‖(lp.single 2 0 (1 : ℂ) : OperatorCoding.CanonicalHilbert)‖ = 1
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

theorem amplifiedCantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    VectorCantorMultiplierEquivalent OperatorCoding.CanonicalHilbert μ ν ↔ μ ≪ ν ∧ ν ≪ μ :=
  vectorCantorMultiplierEquivalent_iff μ ν canonicalHilbertUnitVector canonicalHilbertUnitVector_norm

end MeasureUnitary

#print axioms MeasureUnitary.amplifiedCantorMultiplierEquivalent_iff

