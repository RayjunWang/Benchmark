import CantorHaarComplete

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

abbrev HaarCoefficientSpace := lp (fun _ : Option HaarNodeIndex => ℝ) 2

theorem cantorRealHaarBasis_apply (μ : PositiveCylinderProbabilities) (i : Option HaarNodeIndex) :
    cantorRealHaarBasis μ i = cantorHaarFamily μ i := by
  exact congrFun (HilbertBasis.coe_mk (cantorHaarFamily_orthonormal μ) _) i

def haarLift (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  (cantorRealHaarBasis μ).repr.symm a

theorem norm_haarLift (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    ‖haarLift μ a‖ = ‖a‖ := (cantorRealHaarBasis μ).repr.symm.norm_map a

theorem dist_haarLift (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (haarLift μ a) (haarLift μ b) = dist a b :=
  (cantorRealHaarBasis μ).repr.symm.isometry.dist_eq a b

def haarCoefficientTrunc (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    HaarCoefficientSpace := ∑ i ∈ s, lp.single 2 i (a i)

theorem repr_haar_partial_sum (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    (cantorRealHaarBasis μ).repr (∑ i ∈ s, a i • cantorHaarFamily μ i) =
      haarCoefficientTrunc s a := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, ← cantorRealHaarBasis_apply, HilbertBasis.repr_self]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : Option HaarNodeIndex => ℝ) 2 i (a i) 1).symm

/-- The L2 approximation error is exactly a fixed coefficient-space tail,
independent of the varying measure. -/
theorem norm_haarLift_sub_partial_sum (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    ‖haarLift μ a - ∑ i ∈ s, a i • cantorHaarFamily μ i‖ =
      ‖a - haarCoefficientTrunc s a‖ := by
  rw [← (cantorRealHaarBasis μ).repr.norm_map, map_sub,
    repr_haar_partial_sum]
  simp only [haarLift, LinearIsometryEquiv.apply_symm_apply]

theorem tendsto_haarCoefficientTrunc (a : HaarCoefficientSpace) :
    Tendsto (fun s : Finset (Option HaarNodeIndex) => haarCoefficientTrunc s a) atTop (𝓝 a) :=
  lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) a

def haarFamilyFunction (μ : PositiveCylinderProbabilities)
    (i : Option HaarNodeIndex) (x : HaarCantor) : ℝ :=
  match i with
  | none => 1
  | some i => cantorHaarFunction μ i x

theorem continuous_haarFamilyFunction (i : Option HaarNodeIndex) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCantor =>
      haarFamilyFunction p.1 i p.2) := by
  cases i with
  | none => exact continuous_const
  | some i => exact continuous_cantorHaarFunction i

theorem haarFamilyFunction_coe (μ : PositiveCylinderProbabilities) (i : Option HaarNodeIndex) :
    cantorHaarFamily μ i =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      haarFamilyFunction μ i := by
  cases i with
  | none =>
      simpa only [cantorHaarFamily, cantorOneVector, haarFamilyFunction, indicator_univ] using
        (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
          (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) univ)
          (c := (1 : ℝ)))
  | some i => exact cantorHaarNode_coe μ i

def finiteHaarFunction (s : Finset (Option HaarNodeIndex))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) (x : HaarCantor) : ℝ :=
  ∑ i ∈ s, a i * haarFamilyFunction μ i x

/- Every finite Haar truncation is jointly continuous in weakμ, Hilbert
coefficients and the Cantor point. -/
set_option maxHeartbeats 1500000 in
theorem continuous_finiteHaarFunction (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) × HaarCantor =>
      finiteHaarFunction s p.1.1 p.1.2 p.2) := by
  apply continuous_finsetSum
  intro i _hi
  exact (((lp.lipschitzWith_one_eval 2 i).continuous.comp
    (continuous_snd.comp continuous_fst))).mul
      ((continuous_haarFamilyFunction i).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

#print axioms norm_haarLift_sub_partial_sum
#print axioms continuous_finiteHaarFunction

end BenchmarkJump
