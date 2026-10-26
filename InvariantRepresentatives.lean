import InvariantConditional

/-! Almost-everywhere invariant measurable functions have exactly invariant
measurable representatives for countable group actions. -/

open MeasureTheory ProbabilityTheory Set Filter

namespace MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z] [MulAction G Z]
    (μ : Measure Z)

theorem measurable_invariant_representative (f : Z → ℝ) (hf : Measurable f)
    (haction : ∀ g : G, Measurable (fun z : Z => g • z))
    (hinv : ∀ g : G, (fun z => f (g • z)) =ᵐ[μ] f) :
    ∃ f' : Z → ℝ, Measurable[invariantSigma (G := G)] f' ∧ f' =ᵐ[μ] f := by
  classical
  let S : Set Z := {z | ∀ g : G, f (g • z) = f z}
  have hS : MeasurableSet S := by
    simpa only [S, Function.comp_def, Set.setOf_forall] using
      MeasurableSet.iInter (fun g => measurableSet_eq_fun (hf.comp (haction g)) hf)
  have hgood : ∀ᵐ z ∂μ, z ∈ S := by
    exact ae_all_iff.mpr hinv
  have hSinv (g : G) (z : Z) : g • z ∈ S ↔ z ∈ S := by
    constructor
    · intro hz h
      have hback := hz g⁻¹
      have hh := hz (h*g⁻¹)
      simpa only [mul_smul, inv_smul_smul] using hh.trans hback.symm
    · intro hz h
      have hh : f (h • (g • z)) = f z := by simpa only [mul_smul] using hz (h*g)
      exact hh.trans (hz g).symm
  let f' : Z → ℝ := S.indicator f
  have hf' : Measurable f' := hf.indicator hS
  have hfinv (g : G) (z : Z) : f' (g • z) = f' z := by
    by_cases hz : z ∈ S
    · have hgz := (hSinv g z).mpr hz
      simp only [f', Set.indicator_of_mem hz, Set.indicator_of_mem hgz]
      exact hz g
    · have hgz : g • z ∉ S := fun h => hz ((hSinv g z).mp h)
      simp only [f', Set.indicator_of_notMem hz, Set.indicator_of_notMem hgz]
  refine ⟨f', ?_, ?_⟩
  · intro U hU
    refine ⟨hU.preimage hf', ?_⟩
    intro g
    ext z
    change f' (g • z) ∈ U ↔ f' z ∈ U
    rw [hfinv]
  · exact hgood.mono (fun _ hz => Set.indicator_of_mem hz f)

end MeasureEquivalenceErgodicDecomposition

#print axioms MeasureEquivalenceErgodicDecomposition.measurable_invariant_representative
