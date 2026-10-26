import MeasureUnitaryDensity
import L2ModuleCommutant
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Finite vector-state measures and faithful vectors in actual sigma-finite
L² spaces. These give measure-class reflection without postulating a spectral theorem. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {Ω Λ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace X]

theorem indicatorL2_univ (μ : Measure Ω) (f : Lp ℂ 2 μ) :
    indicatorL2 μ MeasurableSet.univ f = f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ MeasurableSet.univ f] with x hx
  simpa using hx

instance vectorDensityMeasure_finite (μ : Measure Ω) (f : Lp ℂ 2 μ) :
    IsFiniteMeasure (vectorDensityMeasure μ f) := by
  constructor
  rw [vectorDensityMeasure_apply μ MeasurableSet.univ, indicatorL2_univ]
  exact ENNReal.ofReal_lt_top

noncomputable def vectorSpectralState (μ : Measure Ω) (q : Ω → X) (f : Lp ℂ 2 μ) : Measure X :=
  (vectorDensityMeasure μ f).map q

instance vectorSpectralState_finite (μ : Measure Ω) (q : Ω → X) (f : Lp ℂ 2 μ) :
    IsFiniteMeasure (vectorSpectralState μ q f) := by
  unfold vectorSpectralState
  infer_instance

theorem vectorSpectralState_apply (μ : Measure Ω) (q : Ω → X) (hq : Measurable q)
    (f : Lp ℂ 2 μ) {s : Set X} (hs : MeasurableSet s) :
    vectorSpectralState μ q f s =
      ENNReal.ofReal (‖indicatorL2 μ (hs.preimage hq) f‖ ^ 2) := by
  rw [vectorSpectralState, Measure.map_apply hq hs, vectorDensityMeasure_apply]

theorem vectorSpectralState_univ (μ : Measure Ω) (q : Ω → X) (hq : Measurable q)
    (f : Lp ℂ 2 μ) : vectorSpectralState μ q f univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [vectorSpectralState_apply μ q hq f MeasurableSet.univ]
  simp only [preimage_univ, indicatorL2_univ]

theorem faithful_vector_density (μ : Measure Ω) (f : Lp ℂ 2 μ)
    (hf : ∀ᵐ x ∂μ, f x ≠ 0) : μ ≪ vectorDensityMeasure μ f := by
  apply withDensity_absolutelyContinuous'
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const 2).ennreal_ofReal
  · filter_upwards [hf] with x hx
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hx))).ne'

theorem exists_faithful_L2 (μ : Measure Ω) [SigmaFinite μ] :
    ∃ f : Lp ℂ 2 μ, ∀ᵐ x ∂μ, f x ≠ 0 := by
  obtain ⟨ν,hν,hμν,hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  letI : IsFiniteMeasure ν := hν
  let f := rnWeightedMap ν μ hνμ hμν (constantOneL2 ν)
  refine ⟨f,?_⟩
  filter_upwards [rnWeightedMap_coe ν μ hνμ hμν (constantOneL2 ν),
    hμν.ae_eq (constantOneL2_coe ν), rnWeight_inverse_product μ ν hμν hνμ]
    with x hfx h1 hp
  change f x ≠ 0
  rw [hfx,h1]
  apply smul_ne_zero
  · intro hz
    simp [hz] at hp
  · exact one_ne_zero

theorem vectorSpectralState_eq_of_intertwines_generating_projections
    (μ : Measure Ω) (ν : Measure Λ) (q : Ω → X) (r : Λ → X)
    (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (P : Set (Set X)) (hgen : MeasurableSpace.generateFrom P = ‹MeasurableSpace X›)
    (hpi : IsPiSystem P)
    (hP : ∀ s ∈ P, MeasurableSet s)
    (hU : ∀ s, ∀ hsP : s ∈ P, ∀ f : Lp ℂ 2 μ,
      U (indicatorL2 μ ((hP s hsP).preimage hq) f) =
        indicatorL2 ν ((hP s hsP).preimage hr) (U f))
    (f : Lp ℂ 2 μ) : vectorSpectralState μ q f = vectorSpectralState ν r (U f) := by
  apply ext_of_generate_finite P hgen.symm hpi
  · intro s hs
    rw [vectorSpectralState_apply μ q hq f (hP s hs),
      vectorSpectralState_apply ν r hr (U f) (hP s hs), ← hU s hs f, U.norm_map]
  · rw [vectorSpectralState_univ μ q hq, vectorSpectralState_univ ν r hr, U.norm_map]

theorem absolutelyContinuous_push_of_faithful_state
    (μ : Measure Ω) (ν : Measure Λ) (q : Ω → X) (r : Λ → X)
    (hq : Measurable q) (hr : Measurable r)
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (hf : ∀ᵐ x ∂μ, f x ≠ 0)
    (heq : vectorSpectralState μ q f = vectorSpectralState ν r g) :
    μ.map q ≪ ν.map r := by
  have h1 : μ.map q ≪ vectorSpectralState μ q f :=
    (faithful_vector_density μ f hf).map hq
  rw [heq] at h1
  exact h1.trans ((vectorDensityMeasure_absolutelyContinuous ν g).map hr)

theorem vectorSpectralState_integral (μ : Measure Ω) (q : Ω → X) (hq : Measurable q)
    (f : Lp ℂ 2 μ) (c : X → ℂ) (hc : Measurable c) (b : Lp ℂ ∞ μ)
    (hb : b =ᵐ[μ] fun x => c (q x)) :
    (∫ x, c x ∂vectorSpectralState μ q f) =
      inner ℂ f (boundedMultiplierL2 μ b f) := by
  rw [vectorSpectralState, integral_map hq.aemeasurable hc.aestronglyMeasurable,
    vectorDensityMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const 2).ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplierL2_coe μ b f,hb] with x hmul hbx
  rw [hmul,hbx]
  change (ENNReal.ofReal (‖f x‖ ^ 2)).toReal • c (q x) =
    inner ℂ (f x) (c (q x) • f x)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.real_smul, mul_comm, Complex.ofReal_pow]
  rfl

end MeasureUnitary

#print axioms MeasureUnitary.exists_faithful_L2
#print axioms MeasureUnitary.vectorSpectralState_eq_of_intertwines_generating_projections
#print axioms MeasureUnitary.absolutelyContinuous_push_of_faithful_state
#print axioms MeasureUnitary.vectorSpectralState_integral
