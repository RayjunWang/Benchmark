import PositiveConvexNeighborhoods
import MeasureInterpolationEnergy

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish

def positiveMixOn (O : Set PositiveCylinderProbabilities) (hO : PositiveMixConvex O)
    (t : unitInterval) (p : O × O) : O :=
  ⟨positiveProbabilityMix t p.1 p.2, hO t p.1 p.1.property p.2 p.2.property⟩

theorem continuous_positiveMixOn (O : Set PositiveCylinderProbabilities) (hO : PositiveMixConvex O)
    (t : unitInterval) : Continuous (positiveMixOn O hO t) := by
  have hArg : Continuous (fun p : O × O =>
      (t, ((p.1 : PositiveCylinderProbabilities), (p.2 : PositiveCylinderProbabilities)))) :=
    continuous_const.prodMk ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  exact (continuous_positiveProbabilityMix.comp hArg).subtype_mk _

theorem isOpenMap_positiveMixOn (O : Set PositiveCylinderProbabilities) (hOo : IsOpen O)
    (hO : PositiveMixConvex O) (t : unitInterval)
    (hOpen : IsOpenMap (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
      positiveProbabilityMix t p.1 p.2)) : IsOpenMap (positiveMixOn O hO t) :=
  (hOpen.comp (hOo.isOpenMap_subtype_val.prodMap hOo.isOpenMap_subtype_val)).subtype_mk _

/-- The exact finite-chain category step, with the separately checked global
affine-mixture openness theorem supplied explicitly at this interface. -/
theorem measure_interpolation_generic_pairs
    (hOpen : ∀ t : unitInterval, IsOpenMap
      (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
        positiveProbabilityMix t p.1 p.2))
    (O : Set PositiveCylinderProbabilities) (hOo : IsOpen O) (hO : PositiveMixConvex O)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f : PositiveCylinderProbabilities → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ μ ∈ O, ∀ ν ∈ O, μ ∈ D → ν ∈ D →
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2 →
      BoundedDifference (f μ) (f ν)) :
    ∀ᶠ p : O × O in residual (O × O), BoundedDifference (f p.1) (f p.2) := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show 0 < ε ^ 2 / 2 by positivity)
  let m : ℕ := M + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hdiv : 2 / (m : ℝ) < ε ^ 2 := by
    have h : 1 / (m : ℝ) < ε ^ 2 / 2 := by exact_mod_cast hM
    have heq : 2 / (m : ℝ) = 2 * (1 / (m : ℝ)) := by ring
    rw [heq]
    linarith only [h]
  let P (j : Fin (m + 1)) : O × O → O := positiveMixOn O hO (positiveChainParameter m hm j)
  have hDO : ∀ᶠ x : O in residual O, (x : PositiveCylinderProbabilities) ∈ D :=
    eventually_residual_open_subspace O hOo hD
  have hAll : ∀ᶠ p : O × O in residual (O × O),
      ∀ j : Fin (m + 1), (P j p : PositiveCylinderProbabilities) ∈ D := by
    apply eventually_countable_forall.mpr
    intro j
    exact tendsto_residual_of_isOpenMap (continuous_positiveMixOn O hO _)
      (isOpenMap_positiveMixOn O hOo hO _ (hOpen _)) hDO
  filter_upwards [hAll] with p hp
  let u : Fin (m + 1) → RealSequences := fun j => f (P j p)
  have hStep (j : Fin m) : BoundedDifference (u j.castSucc) (u j.succ) := by
    apply hSmall (P j.castSucc p) (P j.castSucc p).property
      (P j.succ p) (P j.succ p).property (hp j.castSucc) (hp j.succ)
    exact (positiveProbabilityMix_chain_step_energy m hm j p.1 p.2).trans_lt hdiv
  have hP0 : P 0 p = p.1 := by
    apply Subtype.ext
    change positiveProbabilityMix (positiveChainParameter m hm 0) p.1 p.2 = p.1
    rw [positiveChainParameter_zero, positiveProbabilityMix_zero]
  have hP1 : P (Fin.last m) p = p.2 := by
    apply Subtype.ext
    change positiveProbabilityMix (positiveChainParameter m hm (Fin.last m)) p.1 p.2 = p.2
    rw [positiveChainParameter_last, positiveProbabilityMix_one]
  have hChain := boundedDifference_fin_chain m u hStep
  change BoundedDifference (f (P 0 p)) (f (P (Fin.last m) p)) at hChain
  rwa [hP0, hP1] at hChain

theorem measure_interpolation_constant_on_open
    (hOpen : ∀ t : unitInterval, IsOpenMap
      (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
        positiveProbabilityMix t p.1 p.2))
    (O : Set PositiveCylinderProbabilities) (hOo : IsOpen O) (hOn : O.Nonempty)
    (hO : PositiveMixConvex O)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f : PositiveCylinderProbabilities → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ μ ∈ O, ∀ ν ∈ O, μ ∈ D → ν ∈ D →
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2 →
      BoundedDifference (f μ) (f ν)) :
    ∃ a : RealSequences, ∀ᶠ μ in residual PositiveCylinderProbabilities,
      μ ∈ O → BoundedDifference (f μ) a := by
  letI : Nonempty O := hOn.to_subtype
  letI : PolishSpace O := hOo.polishSpace
  have hPair := measure_interpolation_generic_pairs hOpen O hOo hO D hD f ε hε hSmall
  obtain ⟨μ, hμ⟩ := exists_residual_section hPair
  refine ⟨f μ, eventually_residual_of_open_subspace O hOo ?_⟩
  filter_upwards [hμ] with ν hν
  exact boundedDifference_equivalence.symm hν

#print axioms measure_interpolation_constant_on_open

end BenchmarkJump
