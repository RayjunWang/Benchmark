import LpCountableAction

/-! A countable orbit match yields exact equality on small Lp local-orbit pairs. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

abbrev TranslationTriples := RealSequences × (Translations p × Translations p)

def tripleFirst (t : TranslationTriples p) : RealSequences × Translations p := (t.1, t.2.1)
def tripleSecond (t : TranslationTriples p) : RealSequences × Translations p := (t.1, t.2.2)
def tripleEndpoints (t : TranslationTriples p) : RealSequences × RealSequences :=
  (translationAction p (tripleFirst p t), translationAction p (tripleSecond p t))

lemma continuous_tripleFirst : Continuous (tripleFirst p) :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)
lemma continuous_tripleSecond : Continuous (tripleSecond p) :=
  continuous_fst.prodMk (continuous_snd.comp continuous_snd)
lemma isOpenMap_tripleFirst : IsOpenMap (tripleFirst p) := IsOpenMap.id.prodMap isOpenMap_fst
lemma isOpenMap_tripleSecond : IsOpenMap (tripleSecond p) := IsOpenMap.id.prodMap isOpenMap_snd
lemma continuous_tripleEndpoints : Continuous (tripleEndpoints p) :=
  ((continuous_translationAction p).comp (continuous_tripleFirst p)).prodMk
    ((continuous_translationAction p).comp (continuous_tripleSecond p))

theorem good_triples
    (U : Set RealSequences) (W : Set (Translations p)) (D : Set RealSequences)
    (hD : D ∈ residual RealSequences) (f : RealSequences → BenchmarkShift.Point)
    (g : BenchmarkShift.Group)
    (hRes : ∀ᶠ a in residual (RealSequences × Translations p),
      a ∈ U ×ˢ W → f (translationAction p a) = BenchmarkShift.shift g (f a.1)) :
    ∀ᶠ t in residual (TranslationTriples p), t ∈ U ×ˢ (W ×ˢ W) →
      tripleEndpoints p t ∈ D ×ˢ D ∧ f (tripleEndpoints p t).1 = f (tripleEndpoints p t).2 := by
  have h1 := tendsto_residual_of_isOpenMap (continuous_tripleFirst p) (isOpenMap_tripleFirst p) hRes
  have h2 := tendsto_residual_of_isOpenMap (continuous_tripleSecond p) (isOpenMap_tripleSecond p) hRes
  have hD1 := tendsto_residual_of_isOpenMap
    ((continuous_translationAction p).comp (continuous_tripleFirst p))
    ((isOpenMap_translationAction p).comp (isOpenMap_tripleFirst p)) hD
  have hD2 := tendsto_residual_of_isOpenMap
    ((continuous_translationAction p).comp (continuous_tripleSecond p))
    ((isOpenMap_translationAction p).comp (isOpenMap_tripleSecond p)) hD
  filter_upwards [h1, h2, hD1, hD2] with t ht1 ht2 htD1 htD2 hrect
  exact ⟨⟨htD1, htD2⟩, (ht1 ⟨hrect.1, hrect.2.1⟩).trans
    (ht2 ⟨hrect.1, hrect.2.2⟩).symm⟩

lemma open_subset_closure_residual {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (O G : Set T) (hOo : IsOpen O) (hG : G ∈ residual T) : O ⊆ closure (O ∩ G) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro V hVo hxV
  obtain ⟨y, ⟨hyV, hyO⟩, hyG⟩ :=
    (dense_of_mem_residual hG).inter_open_nonempty (V ∩ O) (hVo.inter hOo) ⟨x, hxV, hx⟩
  exact ⟨y, hyV, hyO, hyG⟩

lemma equality_of_mem_closure
    (D : Set RealSequences) (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (S : Set (RealSequences × RealSequences)) (hSD : S ⊆ D ×ˢ D)
    (hEq : ∀ q ∈ S, f q.1 = f q.2) (q : RealSequences × RealSequences)
    (hqD : q ∈ D ×ˢ D) (hq : q ∈ closure S) : f q.1 = f q.2 := by
  have hc := ((hf q.1 hqD.1).prodMap (hf q.2 hqD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {r : BenchmarkShift.Point × BenchmarkShift.Point | r.1 = r.2} := hEq
  have hcl := hc.mem_closure hq hm
  simpa only [(isClosed_eq continuous_fst continuous_snd).closure_eq] using hcl

theorem small_translation_exact
    (U : Set RealSequences) (W : Set (Translations p)) (hUo : IsOpen U) (hWo : IsOpen W)
    (D : Set RealSequences) (hD : D ∈ residual RealSequences)
    (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (g : BenchmarkShift.Group)
    (hRes : ∀ᶠ a in residual (RealSequences × Translations p),
      a ∈ U ×ˢ W → f (translationAction p a) = BenchmarkShift.shift g (f a.1))
    (h₀ : Translations p) (hh₀ : h₀ ∈ W) (ε : ℝ) (hBall : Metric.ball h₀ ε ⊆ W)
    (x : RealSequences) (hx : x ∈ U) (k : Translations p) (hk : ‖k‖ < ε)
    (hyD : translationAction p (x, h₀) ∈ D)
    (hzD : translationAction p (x, h₀ + k) ∈ D) :
    f (translationAction p (x, h₀)) = f (translationAction p (x, h₀ + k)) := by
  let Ω : Set (TranslationTriples p) := U ×ˢ (W ×ˢ W)
  let G : Set (TranslationTriples p) := {t | t ∈ Ω →
    tripleEndpoints p t ∈ D ×ˢ D ∧ f (tripleEndpoints p t).1 = f (tripleEndpoints p t).2}
  have hG : G ∈ residual (TranslationTriples p) := good_triples p U W D hD f g hRes
  let S := Ω ∩ G
  have hclosure : Ω ⊆ closure S :=
    open_subset_closure_residual Ω G (hUo.prod (hWo.prod hWo)) hG
  let t : TranslationTriples p := (x, h₀, h₀ + k)
  have ht : t ∈ Ω := by
    refine ⟨hx, hh₀, hBall ?_⟩
    change dist (h₀ + k) h₀ < ε
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hk
  have himg : tripleEndpoints p t ∈ closure (tripleEndpoints p '' S) :=
    image_closure_subset_closure_image (continuous_tripleEndpoints p) ⟨t, hclosure ht, rfl⟩
  apply equality_of_mem_closure D f hf (tripleEndpoints p '' S)
    (fun q hq => ?_) (fun q hq => ?_) (tripleEndpoints p t) ⟨hyD, hzD⟩ himg
  · obtain ⟨s, hs, rfl⟩ := hq
    exact (hs.2 hs.1).1
  · obtain ⟨s, hs, rfl⟩ := hq
    exact (hs.2 hs.1).2

end BenchmarkCountableReverse

#print axioms BenchmarkCountableReverse.small_translation_exact
