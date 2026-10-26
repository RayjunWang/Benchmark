import MeasureUnitaryDensity
import Mathlib.Tactic.Ring

/-! Reflection of equivalence of finite measures from unitary equivalence
of the countable Cantor-cylinder multiplication representations. -/

open MeasureTheory Set Filter

namespace MeasureUnitary

theorem indicatorL2_cantorMultiplier (μ : Measure CantorSpace) (k : CantorCylinderIndex)
    (f : Lp ℂ 2 μ) :
    indicatorL2 μ (cantorCylinder_measurable k) f = (1 / 2 : ℂ) • (f + cantorMultiplier μ k f) := by
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
  · simp only [cantorCylinderPhase, if_pos hxs, indicator_of_mem hxs, one_mul, smul_eq_mul]
    ring
  · simp only [cantorCylinderPhase, if_neg hxs, indicator_of_notMem hxs, neg_one_smul,
      add_neg_cancel, smul_zero]

theorem cantorMultiplier_intertwines_indicators (μ ν : Measure CantorSpace)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ k f, U (cantorMultiplier μ k f) = cantorMultiplier ν k (U f))
    (k : CantorCylinderIndex) (f : Lp ℂ 2 μ) :
    U (indicatorL2 μ (cantorCylinder_measurable k) f) =
      indicatorL2 ν (cantorCylinder_measurable k) (U f) := by
  rw [indicatorL2_cantorMultiplier, U.map_smul, U.map_add, hU, ← indicatorL2_cantorMultiplier]

theorem cantorMultiplier_intertwiner_density (μ ν : Measure CantorSpace) [IsFiniteMeasure μ]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ k f, U (cantorMultiplier μ k f) = cantorMultiplier ν k (U f)) :
    μ = vectorDensityMeasure ν (U (constantOneL2 μ)) := by
  have hmass : ∀ k : CantorCylinderIndex,
      μ (cantorCylinder k) = vectorDensityMeasure ν (U (constantOneL2 μ)) (cantorCylinder k) := by
    intro k
    calc
      μ (cantorCylinder k) = vectorDensityMeasure μ (constantOneL2 μ) (cantorCylinder k) := by
        rw [constantOneL2_density]
      _ = ENNReal.ofReal (‖indicatorL2 μ (cantorCylinder_measurable k) (constantOneL2 μ)‖ ^ 2) :=
        vectorDensityMeasure_apply _ _ _
      _ = ENNReal.ofReal (‖indicatorL2 ν (cantorCylinder_measurable k) (U (constantOneL2 μ))‖ ^ 2) := by
        rw [← cantorMultiplier_intertwines_indicators μ ν U hU, U.norm_map]
      _ = vectorDensityMeasure ν (U (constantOneL2 μ)) (cantorCylinder k) :=
        (vectorDensityMeasure_apply _ _ _).symm
  apply ext_of_generate_finite (Set.range cantorCylinder) cantorCylinder_generates.symm
    cantorCylinder_isPiSystem
  · rintro s ⟨k, rfl⟩
    exact hmass k
  · have h := hmass (⟨∅, Set.univ⟩ : CantorCylinderIndex)
    simpa [cantorCylinder, cylinder] using h

theorem cantorMultiplier_intertwiner_absolutelyContinuous (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ k f, U (cantorMultiplier μ k f) = cantorMultiplier ν k (U f)) : μ ≪ ν := by
  rw [cantorMultiplier_intertwiner_density μ ν U hU]
  exact vectorDensityMeasure_absolutelyContinuous ν _

theorem cantorMultiplierEquivalent_reflects (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : CantorMultiplierEquivalent μ ν) :
    μ ≪ ν ∧ ν ≪ μ := by
  obtain ⟨U, hU⟩ := h
  constructor
  · exact cantorMultiplier_intertwiner_absolutelyContinuous μ ν U hU
  · apply cantorMultiplier_intertwiner_absolutelyContinuous ν μ U.symm
    intro k f
    apply U.injective
    simpa using (hU k (U.symm f)).symm

theorem cantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    CantorMultiplierEquivalent μ ν ↔ μ ≪ ν ∧ ν ≪ μ :=
  ⟨cantorMultiplierEquivalent_reflects μ ν,
    fun h => equivalentMeasures_cantorMultiplierEquivalent μ ν h.1 h.2⟩

end MeasureUnitary

#print axioms MeasureUnitary.cantorMultiplierEquivalent_iff
