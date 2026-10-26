import RootContinuity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Restricting a square-density measure is continuous in its L2 root.
This supports extension of measurable-set invariance from a dense subgroup. -/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedRoots

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z] (M : Measure Z)
    [IsFiniteMeasure M] {s : Set Z} (hs : MeasurableSet s)

def cutRoot : Lp ℝ 2 M →L[ℝ] Lp ℝ 2 M :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL M ∞ 2 2
    (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ))

theorem cutRoot_coe (f : Lp ℝ 2 M) :
    cutRoot M hs f =ᵐ[M] s.indicator (fun z => f z) := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
    (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ)) f,
    indicatorConstLp_coeFn (p := ∞) (hs := hs) (hμs := measure_ne_top M s)
      (c := (1:ℝ))] with z hmul hind
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2
    (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ)) f) z = _
  rw [hmul]
  change (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ)) z * f z = _
  rw [hind]
  by_cases hz : z ∈ s <;> simp [hz]

theorem squareMeasure_cutRoot (f : Lp ℝ 2 M) :
    (squareMeasure M (cutRoot M hs f) : Measure Z) =
      (squareMeasure M f : Measure Z).restrict s := by
  change M.withDensity (fun z => ENNReal.ofReal ((cutRoot M hs f) z ^ 2)) =
    (M.withDensity (fun z => ENNReal.ofReal (f z ^ 2))).restrict s
  have hfun : (fun z => ENNReal.ofReal ((cutRoot M hs f) z ^ 2)) =ᵐ[M]
      s.indicator (fun z => ENNReal.ofReal (f z ^ 2)) := by
    filter_upwards [cutRoot_coe M hs f] with z hz
    rw [hz]
    by_cases hzs : z ∈ s <;> simp [hzs]
  rw [withDensity_congr_ae hfun, withDensity_indicator hs, ← restrict_withDensity hs]

def restrictedSquareMeasure (f : Lp ℝ 2 M) : FiniteMeasure Z :=
  squareMeasure M (cutRoot M hs f)

theorem restrictedSquareMeasure_continuous [TopologicalSpace Z] [BorelSpace Z] :
    Continuous (restrictedSquareMeasure M hs) :=
  (squareMeasure_continuous M).comp (cutRoot M hs).continuous

include hs in
omit [IsFiniteMeasure M] in
theorem ae_eq_of_restrict_eq {t : Set Z} (ht : MeasurableSet t)
    (h : M.restrict s = M.restrict t) : s =ᵐ[M] t := by
  have hs0 : M (s \ t) = 0 := by
    have he := congrArg (fun ν : Measure Z => ν (s \ t)) h
    simpa only [Measure.restrict_apply (hs.diff ht), Set.diff_inter_self,
      Set.inter_eq_left.mpr Set.diff_subset, measure_empty] using he
  have ht0 : M (t \ s) = 0 := by
    have he := congrArg (fun ν : Measure Z => ν (t \ s)) h.symm
    simpa only [Measure.restrict_apply (ht.diff hs), Set.diff_inter_self,
      Set.inter_eq_left.mpr Set.diff_subset, measure_empty] using he
  rw [Filter.eventuallyEq_set]
  have ha : ∀ᵐ z ∂M, z ∉ s \ t := by simpa only [ae_iff, not_not] using hs0
  have hb : ∀ᵐ z ∂M, z ∉ t \ s := by simpa only [ae_iff, not_not] using ht0
  filter_upwards [ha, hb] with z haz hbz
  simp only [Set.mem_diff, not_and] at haz hbz
  constructor <;> intro hz
  · by_contra hzt
    exact haz hz hzt
  · by_contra hzs
    exact hbz hz hzs

include hs in
omit [IsFiniteMeasure M] in
theorem invariant_iff_restrict_map (e : Z ≃ᵐ Z) :
    (e ⁻¹' s) =ᵐ[M] s ↔ (M.map e).restrict s = (M.restrict s).map e := by
  rw [e.restrict_map]
  constructor
  · intro h
    exact congrArg (Measure.map e) (Measure.restrict_congr_set h)
  · intro h
    exact ae_eq_of_restrict_eq M (hs.preimage e.measurable) hs
      (e.measurableEmbedding.map_injective h)

section Action

variable {K : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]

def finiteOrbit (ν : Measure Z) [IsFiniteMeasure ν] (g : K) : FiniteMeasure Z :=
  ⟨ν.map (fun z => g • z), inferInstance⟩

theorem finiteOrbit_continuous (ν : Measure Z) [IsFiniteMeasure ν] :
    Continuous (finiteOrbit (K := K) ν) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have he : (fun g : K => ∫ z, f z ∂(finiteOrbit ν g : Measure Z)) =
      fun g : K => ∫ z, f (g • z) ∂ν := by
    funext g
    exact integral_map_equiv (MeasurableEquiv.smul g) f
  rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro g
    exact (f.continuous.comp (continuous_const_smul g)).aestronglyMeasurable
  · intro g
    exact Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm (g • z))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall
      (fun z => f.continuous.comp (continuous_id.smul continuous_const))

end Action

end MeasureEquivalenceRestrictedRoots

#print axioms MeasureEquivalenceRestrictedRoots.squareMeasure_cutRoot
#print axioms MeasureEquivalenceRestrictedRoots.restrictedSquareMeasure_continuous
