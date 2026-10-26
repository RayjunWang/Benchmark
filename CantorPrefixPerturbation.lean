import CantorSmallCylinders
import CantorProbabilityCoordinates

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

def prefixPoint {n : ℕ} (s : Fin n → Bool) : HaarCantor :=
  fun i => if hi : i < n then s ⟨i,hi⟩ else false

theorem prefixPoint_mem {n : ℕ} (s : Fin n → Bool) : prefixPoint s ∈ prefixCylinder s := by
  intro i
  simp [prefixPoint,i.isLt]

def prefixRedirect (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) (x : HaarCantor) : HaarCantor :=
  prefixPoint (smallMassPrefix μ (fun i : Fin n => x i) m)

theorem continuous_prefixRedirect (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    Continuous (prefixRedirect μ n m) := by
  exact (continuous_of_discreteTopology (f := fun s : Fin n → Bool => prefixPoint (smallMassPrefix μ s m))).comp
    (continuous_pi fun i : Fin n => continuous_apply (i : ℕ))

theorem prefixRedirect_eq (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) (x : HaarCantor)
    (i : ℕ) (hi : i < n) : prefixRedirect μ n m x i = x i := by
  exact (smallMassPrefix_subset μ (fun j : Fin n => x j) m
    (prefixPoint_mem (smallMassPrefix μ (fun j : Fin n => x j) m))) ⟨i,hi⟩

theorem prefixCylinder_pairwise_disjoint (n : ℕ) :
    Pairwise (fun (s t : Fin n → Bool) => Disjoint (prefixCylinder s) (prefixCylinder t)) := by
  intro s t hst
  apply disjoint_left.mpr
  intro x hs ht
  apply hst
  funext i
  exact (hs i).symm.trans (ht i)

theorem prefixCylinder_iUnion (n : ℕ) : (⋃ s : Fin n → Bool, prefixCylinder s) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨fun i => x i, fun _ => rfl⟩

theorem prefixCylinder_mass_sum (μ : ProbabilityMeasure HaarCantor) (n : ℕ) :
    ∑ s : Fin n → Bool, (μ : Measure HaarCantor).real (prefixCylinder s) = 1 := by
  rw [← measureReal_iUnion_fintype (prefixCylinder_pairwise_disjoint n)
    (fun s => (isClopen_prefixCylinder s).isClosed.measurableSet), prefixCylinder_iUnion]
  simp

def smallPrefixRegion (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) : Set HaarCantor :=
  ⋃ s : Fin n → Bool, prefixCylinder (smallMassPrefix μ s m)

theorem smallPrefixRegion_clopen (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    IsClopen (smallPrefixRegion μ n m) :=
  isClopen_iUnion_of_finite (fun s => isClopen_prefixCylinder (smallMassPrefix μ s m))

theorem smallPrefixRegion_mass_bound (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    (μ : Measure HaarCantor).real (smallPrefixRegion μ n m) ≤ (1 / 2 : ℝ) ^ m := by
  calc
    _ ≤ ∑ s : Fin n → Bool, (μ : Measure HaarCantor).real (prefixCylinder (smallMassPrefix μ s m)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ s : Fin n → Bool, (1 / 2 : ℝ) ^ m * (μ : Measure HaarCantor).real (prefixCylinder s) :=
      Finset.sum_le_sum (fun s _ => smallMassPrefix_bound μ s m)
    _ = _ := by rw [← Finset.mul_sum, prefixCylinder_mass_sum, mul_one]

theorem prefixRedirect_mem_smallPrefixRegion (μ : ProbabilityMeasure HaarCantor)
    (n m : ℕ) (x : HaarCantor) : prefixRedirect μ n m x ∈ smallPrefixRegion μ n m :=
  mem_iUnion.mpr ⟨fun i : Fin n => x i, prefixPoint_mem _⟩

def redirectedProbability (μ ν : ProbabilityMeasure HaarCantor) (n m : ℕ) : ProbabilityMeasure HaarCantor :=
  ⟨(ν : Measure HaarCantor).map (prefixRedirect μ n m),
    Measure.isProbabilityMeasure_map (continuous_prefixRedirect μ n m).measurable.aemeasurable⟩

theorem redirectedProbability_cylinder (μ ν : ProbabilityMeasure HaarCantor)
    (n m : ℕ) (k : MeasureUnitary.CantorCylinderIndex) (hk : ∀ i ∈ k.1, i < n) :
    (redirectedProbability μ ν n m : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) =
      (ν : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) := by
  rw [show (redirectedProbability μ ν n m : Measure HaarCantor) =
    (ν : Measure HaarCantor).map (prefixRedirect μ n m) from rfl,
    Measure.map_apply (continuous_prefixRedirect μ n m).measurable (MeasureUnitary.cantorCylinder_measurable k)]
  congr 1
  ext x
  change ((fun i : k.1 => prefixRedirect μ n m x i) ∈ k.2) ↔ ((fun i : k.1 => x i) ∈ k.2)
  have he : (fun i : k.1 => prefixRedirect μ n m x i) = (fun i : k.1 => x i) := by
    funext i
    exact prefixRedirect_eq μ n m x i (hk i i.property)
  rw [he]

theorem redirectedProbability_tendsto (μ ν : ProbabilityMeasure HaarCantor) (m : ℕ) :
    Tendsto (fun n => redirectedProbability μ ν n m) atTop (𝓝 ν) := by
  apply (tendsto_cantorProbability_iff _ _).mpr
  intro k
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (k.1.sup id)] with n hn
  apply congrArg ENNReal.toReal
  exact (redirectedProbability_cylinder μ ν n m k (fun i hi =>
    (Finset.le_sup (f := id) hi).trans_lt hn)).symm

end BenchmarkJump

#print axioms BenchmarkJump.redirectedProbability_tendsto
