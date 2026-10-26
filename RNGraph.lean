import DensityMeasure
import HellingerTransport
import DensityGraphCompleteness
import PolishGroupTopology
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Action

open MeasureTheory Filter Set
open scoped Topology

namespace MeasureEquivalenceRNGraph

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z]

theorem squareMeasure_root (M ν : Measure Z) [SigmaFinite M] [IsFiniteMeasure ν]
    (hν : ν ≪ M) : (squareMeasure M (root ν M) : Measure Z) = ν := by
  change M.withDensity (fun x => ENNReal.ofReal ((root ν M) x ^ 2)) = ν
  calc
    _ = M.withDensity (ν.rnDeriv M) := by
      apply withDensity_congr_ae
      filter_upwards [root_coe ν M, Measure.rnDeriv_ne_top ν M] with x hx htop
      rw [hx, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop]
    _ = ν := Measure.withDensity_rnDeriv_eq ν M hν

section Action

variable {K : Type*} [CommGroup K] [TopologicalSpace K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]

noncomputable def orbit (g : K) : FiniteMeasure Z :=
  ⟨M.map (fun z => g • z), inferInstance⟩

instance orbit_isProbability (g : K) : IsProbabilityMeasure (orbit M g : Measure Z) := by
  change IsProbabilityMeasure (M.map (fun z => g • z))
  exact M.isProbabilityMeasure_map (measurable_const_smul g).aemeasurable

theorem orbit_continuous [FirstCountableTopology K] : Continuous (orbit (K := K) M) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hrep : (fun g : K => ∫ z, f z ∂(orbit M g : Measure Z)) =
      fun g : K => ∫ z, f (g • z) ∂M := by
    funext g
    exact integral_map_equiv (MeasurableEquiv.smul g) f
  rw [hrep]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro g
    exact (f.continuous.comp (continuous_const_smul g)).aestronglyMeasurable
  · intro g
    exact Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm (g • z))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun z => f.continuous.comp (continuous_id.smul continuous_const))

omit [IsProbabilityMeasure M] in
theorem map_orbit (g h : K) :
    (M.map (fun z => h • z)).map (fun z => g • z) = M.map (fun z => (g * h) • z) := by
  rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
  congr 1
  funext z
  exact (mul_smul g h z).symm

/-- Exact quasi-invariance subgroup, tested by forward and inverse one-sided AC. -/
def quasiInvariantSubgroup : Subgroup K where
  carrier := {g | M.map (fun z => g • z) ≪ M ∧ M.map (fun z => g⁻¹ • z) ≪ M}
  one_mem' := by simpa using (And.intro (Measure.AbsolutelyContinuous.refl M) (Measure.AbsolutelyContinuous.refl M))
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [← map_orbit M g h]
      exact ((MeasurableEquiv.smul g).measurableEmbedding.absolutelyContinuous_map hh.1).trans hg.1
    · rw [mul_inv_rev, ← map_orbit M h⁻¹ g⁻¹]
      exact ((MeasurableEquiv.smul h⁻¹).measurableEmbedding.absolutelyContinuous_map hg.2).trans hh.2
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

omit [IsProbabilityMeasure M] in
theorem mem_quasiInvariantSubgroup_iff (g : K) :
    g ∈ quasiInvariantSubgroup (K := K) M ↔
      M.map (fun z => g • z) ≪ M ∧ M ≪ M.map (fun z => g • z) := by
  exact (MeasureEquivalenceInverseAC.mutual_ac_iff_forward_inverse M
    (MeasurableEquiv.smul g)).symm

noncomputable def feature (h : quasiInvariantSubgroup (K := K) M) : positiveUnitSphere M :=
  ⟨root (orbit M (h : K) : Measure Z) M,
    root_nonnegative _ _, root_probability_norm _ _ h.property.1⟩

theorem feature_factor (h : quasiInvariantSubgroup (K := K) M) :
    squareMeasure M (feature M h : Lp ℝ 2 M) = orbit M (h : K) := by
  apply Subtype.ext
  exact squareMeasure_root M _ h.property.1

theorem feature_inverse (h k : quasiInvariantSubgroup (K := K) M) :
    dist (feature M h⁻¹) (feature M k⁻¹) = dist (feature M h) (feature M k) := by
  apply root_dist_inverse (MeasurableEquiv.smul (h : K)) (MeasurableEquiv.smul (k : K)) M
  · intro z
    exact smul_comm (h : K) (k : K) z
  · exact h.property.1
  · exact k.property.1
  · exact h.property.2
  · exact k.property.2

theorem feature_mul_left (a h k : quasiInvariantSubgroup (K := K) M) :
    dist (feature M (a * h)) (feature M (a * k)) = dist (feature M h) (feature M k) := by
  have hd := root_dist_map (MeasurableEquiv.smul (a : K))
    (orbit M (h : K) : Measure Z) (orbit M (k : K) : Measure Z) M
    h.property.1 k.property.1 a.property.1
  change dist (root ((M.map (fun z => (h : K) • z)).map (fun z => (a : K) • z)) M)
    (root ((M.map (fun z => (k : K) • z)).map (fun z => (a : K) • z)) M) =
    dist (root (M.map (fun z => (h : K) • z)) M)
      (root (M.map (fun z => (k : K) • z)) M) at hd
  simp only [map_orbit] at hd
  exact hd

end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]

noncomputable def graphMap (h : quasiInvariantSubgroup (K := K) M) :
    K × positiveUnitSphere M := ((h : K), feature M h)

theorem isClosed_graph : IsClosed (Set.range (graphMap (K := K) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  apply MeasureEquivalenceDensityGraph.isClosed_density_graph
    (quasiInvariantSubgroup M) (feature M) (orbit M)
    (fun v : positiveUnitSphere M => squareMeasure M v)
    (fun ν : FiniteMeasure Z => (ν : Measure Z) ≪ M)
  · exact orbit_continuous M
  · exact (squareMeasure_continuous M).comp continuous_subtype_val
  · intro v w hvw
    apply Subtype.ext
    exact squareMeasure_injective_nonnegative M v.property.1 w.property.1 hvw
  · exact feature_factor M
  · intro v
    exact squareMeasure_ac M v
  · intro g
    rfl
  · exact feature_inverse M

theorem isComplete_graph [CompleteSpace K] :
    IsComplete (Set.range (graphMap (K := K) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  exact (isClosed_graph M).isComplete

theorem completeSpace_graph [CompleteSpace K] :
    CompleteSpace (Set.range (graphMap (K := K) M)) :=
  (isComplete_graph M).completeSpace_coe

end Graph

end MeasureEquivalenceRNGraph

#print axioms MeasureEquivalenceRNGraph.squareMeasure_root
#print axioms MeasureEquivalenceRNGraph.orbit_continuous
#print axioms MeasureEquivalenceRNGraph.mem_quasiInvariantSubgroup_iff
#print axioms MeasureEquivalenceRNGraph.feature_factor
#print axioms MeasureEquivalenceRNGraph.feature_inverse
#print axioms MeasureEquivalenceRNGraph.feature_mul_left
#print axioms MeasureEquivalenceRNGraph.isClosed_graph
#print axioms MeasureEquivalenceRNGraph.completeSpace_graph
