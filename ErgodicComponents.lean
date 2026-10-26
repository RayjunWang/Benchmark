import GroupMarkov
import InvariantRepresentatives
import TestSetErgodicity

/-! Actual ergodicity of almost every invariant conditional probability,
using one global Markov contraction and a mean-ergodic subsequence. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MeasureEquivalenceErgodicDecomposition

open MeasureEquivalenceMarkov

variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableEq Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z] in
theorem restricted_stationary_of_noLeak
    (ν : Measure Z) [IsFiniteMeasure ν] (P : Kernel Z Z) [IsMarkovKernel P]
    (hstat : P ∘ₘ ν = ν) (B : Set Z) (hB : MeasurableSet B)
    (hleak : ∀ᵐ z ∂ν, ∀ᵐ y ∂P z, y ∈ B ↔ z ∈ B) :
    P ∘ₘ ν.restrict B = ν.restrict B := by
  ext A hA
  rw [Measure.bind_apply hA P.aemeasurable, Measure.restrict_apply hA]
  exact (setLIntegral_of_stationary_noLeak ν P hstat B A hB hA hleak).trans
    (congrArg ν (inter_comm B A))

omit [MeasurableEq Z] in
/-- For each L2 input, one actual kernel-average subsequence has a
constant limit on almost every conditional component. -/
theorem exists_constant_average_limit_on_components (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ c : ℝ,
      ∀ᵐ z ∂invariantConditionalKernel (G := G) μ x,
        Tendsto (fun n => kernelAverage
          (metropolisKernel μ (groupMoves (G := G)) (groupMoves_ac μ hns)) f (ns n) z)
          atTop (𝓝 c) := by
  let e : ℕ → Z ≃ᵐ Z := groupMoves (G := G)
  let hm : ∀ n, μ.map (e n) ≪ μ := groupMoves_ac μ hns
  let P := metropolisKernel μ e hm
  let L := normalizedMetropolisTransition μ e hm
  let v : Lp ℝ 2 μ := (LinearMap.eqLocus L 1).orthogonalProjection (hf.toLp f)
  have hL : ∀ u : Lp ℝ 2 μ, L u =ᵐ[μ] kernelApply P u :=
    fun u => normalizedMetropolisTransition_ae_eq_kernel μ e hm u
  obtain ⟨ns, hmono, hlim⟩ := exists_kernelAverage_subseq_tendsto_ae μ P
    (metropolisKernel_stationary μ e hm) L hL
    (normalizedMetropolisTransition_norm_le_one μ e hm) f hf
  have hvfix : L v = v := ((LinearMap.eqLocus L 1).orthogonalProjection (hf.toLp f)).property
  have hvinv : ∀ g : G, (fun z => v (g • z)) =ᵐ[μ] v :=
    (groupTransition_fixed_iff μ hns v).mp hvfix
  obtain ⟨v', hv'm, hv'eq⟩ := measurable_invariant_representative μ v
    (Lp.stronglyMeasurable v).measurable (fun g => measurable_const_smul g) hvinv
  have hlim' : ∀ᵐ z ∂μ,
      Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 (v' z)) := by
    filter_upwards [hlim, hv'eq] with z hz heq
    rwa [heq]
  have hcomp := Measure.ae_ae_of_ae_comp
    (by rwa [invariantConditionalKernel_comp] :
      ∀ᵐ z ∂invariantConditionalKernel (G := G) μ ∘ₘ μ,
        Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 (v' z)))
  have hc := conditional_fiber_constant μ (v' : InvariantBase G Z → ℝ) hv'm
  filter_upwards [hcomp, hc] with x hx hcx
  refine ⟨ns, hmono, v' x, ?_⟩
  filter_upwards [hx, hcx] with z hz hcz
  change v' z = v' x at hcz
  rwa [hcz] at hz

include hns in
/-- The invariant conditional probabilities of a finite nonsingular
countable action are ergodic almost everywhere. The almost-everywhere
quantifier is outside the test over all invariant measurable sets. -/
theorem invariantConditionalKernel_ergodic :
    ∀ᵐ x ∂μ, ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' B = B) →
      invariantConditionalKernel (G := G) μ x B = 0 ∨
        invariantConditionalKernel (G := G) μ x Bᶜ = 0 := by
  classical
  let e : ℕ → Z ≃ᵐ Z := groupMoves (G := G)
  let hm : ∀ n, μ.map (e n) ≪ μ := groupMoves_ac μ hns
  let P := metropolisKernel μ e hm
  let κ := invariantConditionalKernel (G := G) μ
  have hstat : P ∘ₘ μ = μ := metropolisKernel_stationary μ e hm
  have hκstat : ∀ᵐ x ∂μ, P ∘ₘ κ x = κ x := by
    apply invariantConditionalKernel_stationary μ P hstat
    intro B _hB hB
    exact groupKernel_noLeak μ hns B hB
  have hMoves : ∀ᵐ z ∂μ, ∀ᵐ y ∂P z, moveRelation e z y :=
    metropolisKernel_ae_moves μ e hm
  have hκMoves : ∀ᵐ x ∂μ, ∀ᵐ z ∂κ x, ∀ᵐ y ∂P z, moveRelation e z y := by
    apply Measure.ae_ae_of_ae_comp
    rwa [invariantConditionalKernel_comp]
  let test : Finset ℕ → Z → ℝ := fun s => (determiningSet s).indicator (fun _ => (1 : ℝ))
  have htestm (s : Finset ℕ) : Measurable (test s) :=
    measurable_const.indicator (determiningSet_measurable s)
  have htestb (s : Finset ℕ) : ∀ z, |test s z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ determiningSet (Z := Z) s
    · simp [test, Set.indicator_of_mem hz]
    · simp [test, Set.indicator_of_notMem hz]
  have htestLp (s : Finset ℕ) : MemLp (test s) 2 μ :=
    (memLp_const (1 : ℝ)).indicator (determiningSet_measurable s)
  have htests : ∀ s : Finset ℕ, ∀ᵐ x ∂μ,
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ c : ℝ,
        ∀ᵐ z ∂κ x, Tendsto (fun n => kernelAverage P (test s) (ns n) z) atTop (𝓝 c) := by
    intro s
    exact exists_constant_average_limit_on_components μ hns (test s) (htestLp s)
  have htestsAll := ae_all_iff.mpr htests
  filter_upwards [hκstat, hκMoves, htestsAll] with x hxstat hxMoves hxTests
  intro B hB hBinv
  let ν := κ x
  have hBmoves : ∀ n, (e n) ⁻¹' B = B := by
    intro n
    simpa only [e, groupMoves, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply] using
      hBinv (groupEnumeration G n)⁻¹
  have hnoLeak : ∀ᵐ z ∂ν, ∀ᵐ y ∂P z, y ∈ B ↔ z ∈ B := by
    filter_upwards [hxMoves] with z hz
    exact hz.mono (fun y hy => moveRelation_mem_iff e B hBmoves hy)
  have hBstat : P ∘ₘ ν.restrict B = ν.restrict B :=
    restricted_stationary_of_noLeak ν P hxstat B hB hnoLeak
  apply zero_or_conull_of_test_factorization ν B hB
  intro s
  obtain ⟨ns, hnsmono, c, hclim⟩ := hxTests s
  have hBint := setIntegral_eq_mul_of_kernelAverage_limit ν P B hBstat
    (test s) (htestm s) 1 zero_le_one (htestb s) ns hnsmono c hclim
  have hUint := setIntegral_eq_mul_of_kernelAverage_limit ν P Set.univ
    (by simpa only [Measure.restrict_univ] using hxstat)
    (test s) (htestm s) 1 zero_le_one (htestb s) ns hnsmono c hclim
  have hc : ν.real (determiningSet (Z := Z) s) = c := by
    simpa only [test, Measure.restrict_univ,
      integral_indicator_const (1 : ℝ) (determiningSet_measurable s),
      smul_eq_mul, mul_one, probReal_univ] using hUint
  have hleft : (∫ z in B, test s z ∂ν) = ν.real (determiningSet (Z := Z) s ∩ B) := by
    change (∫ z, (determiningSet (Z := Z) s).indicator (fun _ => (1 : ℝ)) z ∂ν.restrict B) = _
    rw [integral_indicator_const (1 : ℝ) (determiningSet_measurable s),
      measureReal_restrict_apply (determiningSet_measurable s), smul_eq_mul, mul_one]
  rw [hleft, ← hc] at hBint
  exact hBint

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.exists_constant_average_limit_on_components
#print axioms MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_ergodic
