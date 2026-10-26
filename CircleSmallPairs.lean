import CircleRowCover

open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable

abbrev CircleTriples := CircleSequences × (NullCircleGroup × NullCircleGroup)

def tripleFirst (t : CircleTriples) : CircleSequences × NullCircleGroup :=
  (t.1, t.2.1)

def tripleSecond (t : CircleTriples) : CircleSequences × NullCircleGroup :=
  (t.1, t.2.2)

def tripleEndpoints (t : CircleTriples) : CircleSequences × CircleSequences :=
  (circleAction (tripleFirst t), circleAction (tripleSecond t))

theorem continuous_tripleFirst : Continuous tripleFirst :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)

theorem continuous_tripleSecond : Continuous tripleSecond :=
  continuous_fst.prodMk (continuous_snd.comp continuous_snd)

theorem isOpenMap_tripleFirst : IsOpenMap tripleFirst :=
  IsOpenMap.id.prodMap isOpenMap_fst

theorem isOpenMap_tripleSecond : IsOpenMap tripleSecond :=
  IsOpenMap.id.prodMap isOpenMap_snd

theorem continuous_tripleEndpoints : Continuous tripleEndpoints :=
  (continuous_circleAction.comp continuous_tripleFirst).prodMk
    (continuous_circleAction.comp continuous_tripleSecond)

/-- The two row matches imply a uniform same-row bound for a comeager set
of triples, while both endpoints may additionally be required in D. -/
theorem circle_good_triples
    (U : Set CircleSequences) (W : Set NullCircleGroup) (D : Set CircleSequences)
    (hD : D ∈ residual CircleSequences) (f g : CircleSequences → RealSequences)
    (n : ℕ)
    (hRes : ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
      p ∈ U ×ˢ W → UniformBound n (f (circleAction p)) (g p.1)) :
    ∀ᶠ t in residual CircleTriples,
      t ∈ U ×ˢ (W ×ˢ W) →
        tripleEndpoints t ∈ D ×ˢ D ∧
        UniformBound (2 * n) (f (tripleEndpoints t).1) (f (tripleEndpoints t).2) := by
  have h1 := tendsto_residual_of_isOpenMap continuous_tripleFirst isOpenMap_tripleFirst hRes
  have h2 := tendsto_residual_of_isOpenMap continuous_tripleSecond isOpenMap_tripleSecond hRes
  have hD1 := tendsto_residual_of_isOpenMap
    (continuous_circleAction.comp continuous_tripleFirst)
    (isOpenMap_circleAction.comp isOpenMap_tripleFirst) hD
  have hD2 := tendsto_residual_of_isOpenMap
    (continuous_circleAction.comp continuous_tripleSecond)
    (isOpenMap_circleAction.comp isOpenMap_tripleSecond) hD
  filter_upwards [h1, h2, hD1, hD2] with t ht1 ht2 htD1 htD2 htRect
  refine ⟨⟨htD1, htD2⟩, ?_⟩
  have hB1 := ht1 ⟨htRect.1, htRect.2.1⟩
  have hB2 := ht2 ⟨htRect.1, htRect.2.2⟩
  have hB := uniformBound_trans hB1 (uniformBound_symm hB2)
  simpa only [two_mul] using hB

theorem mem_closure_inter_of_residual {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (O G : Set T) (hOo : IsOpen O) (hG : G ∈ residual T) :
    O ⊆ closure (O ∩ G) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro V hVo hxV
  obtain ⟨y, ⟨hyV, hyO⟩, hyG⟩ :=
    (dense_of_mem_residual hG).inter_open_nonempty (V ∩ O) (hVo.inter hOo) ⟨x, hxV, hx⟩
  exact ⟨y, hyV, hyO, hyG⟩

/-- Closed uniform output bounds extend along limits of pairs inside the
relative continuity set, exactly as used by the manuscript's closure step. -/
theorem uniformBound_of_mem_closure {D : Set CircleSequences}
    (f : CircleSequences → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ) (S : Set (CircleSequences × CircleSequences))
    (hSD : S ⊆ D ×ˢ D)
    (hBound : ∀ p ∈ S, UniformBound n (f p.1) (f p.2))
    (p : CircleSequences × CircleSequences) (hpD : p ∈ D ×ˢ D)
    (hp : p ∈ closure S) : UniformBound n (f p.1) (f p.2) := by
  have hc := ((hf p.1 hpD.1).prodMap (hf p.2 hpD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {q : RealSequences × RealSequences | UniformBound n q.1 q.2} := hBound
  have hcl := hc.mem_closure hp hm
  simpa only [(isClosed_uniformBound n).closure_eq] using hcl

theorem norm_trunc0_le (s : Finset ℕ) (t : CircleSequences) (δ : ℝ)
    (hδ : 0 ≤ δ) (ht : ∀ i, ‖t i‖ ≤ δ) :
    ‖trunc0 s t‖ ≤ δ := by
  change ‖trunc ⊤ s t‖ ≤ δ
  apply lp.norm_le_of_forall_le hδ
  intro i
  rw [trunc_apply]
  split_ifs
  · exact ht i
  · simpa using hδ

theorem nullCircleCoordinates_add (h₁ h₂ : NullCircleGroup) :
    nullCircleCoordinates (h₁ + h₂) = nullCircleCoordinates h₁ + nullCircleCoordinates h₂ := rfl

theorem tendsto_truncated_endpoint (x y : CircleSequences) (h₀ : NullCircleGroup) :
    Tendsto
      (fun N : ℕ => circleAction
        (x, h₀ + trunc0 (Finset.range N) (y - circleAction (x, h₀))))
      atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  change y i = x i + (nullCircleCoordinates h₀ i +
    trunc ⊤ (Finset.range N) (y - circleAction (x, h₀)) i)
  rw [trunc_apply]
  simp only [Finset.mem_range, hN, ite_true, Pi.sub_apply, circleAction, Pi.add_apply,
    nullCircleCoordinates]
  abel

#print axioms circle_good_triples
#print axioms uniformBound_of_mem_closure
#print axioms tendsto_truncated_endpoint

end BenchmarkJump
