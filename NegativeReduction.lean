import CompactAveraging
import RNPresentation
import CirclePresentation
import TailGraphObstruction

/-! Actual negative Borel-reducibility statements, assembled from the
compact probability kernel, concrete RN graph, and concrete circle grids. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceNegative

open MeasureEquivalenceResearch MeasureEquivalenceCompactAveraging
open MeasureEquivalenceRNGraph MeasureEquivalenceRNPresentation MeasureEquivalenceHellinger
open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology
open MeasureEquivalenceCirclePresentation MeasureEquivalenceCircleReduction
open MeasureEquivalenceTail

variable {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem c0_reduction_impossible (f : (ℕ → ℝ) → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, RealNullRel x y ↔
      EquivalentMeasures (f x : Measure Y) (f y : Measure Y)) : False := by
  let : PolishSpace (Multiplicative K) := inferInstanceAs (PolishSpace K)
  let := upgradeIsCompletelyMetrizable (Multiplicative K)
  let := baseTranslationAction K Y
  let := continuous_baseTranslationAction K Y
  let := h0_polish
  let : PolishSpace (Multiplicative H0) := inferInstanceAs (PolishSpace H0)
  let : MeasurableSpace (Multiplicative H0) := borel (Multiplicative H0)
  let : BorelSpace (Multiplicative H0) := ⟨rfl⟩
  let F : K → ProbabilityMeasure Y := f ∘ realEmbed
  have hF : Measurable F := hf.comp continuous_realEmbed.measurable
  have hFred : ∀ x y, EquivalentMeasures (F x : Measure Y) (F y : Measure Y) ↔
      x - y ∈ h0Image := by
    intro x y
    exact (h0_compose_reduction (fun μ ν : ProbabilityMeasure Y =>
      EquivalentMeasures (μ : Measure Y) (ν : Measure Y)) f hred x y).symm
  obtain ⟨M, hM, hMQ⟩ := torus_polish_action_averaging h0Image F hF hFred
  let := hM
  let i : Multiplicative H0 →* Multiplicative K :=
    AddMonoidHom.toMultiplicative h0Inclusion
  have hi : Continuous i := h0Inclusion_continuous
  have hinj : Function.Injective i := h0Inclusion_injective
  have hrange : Set.range i = (quasiInvariantSubgroup (K := Multiplicative K) M : Set _) := by
    ext g
    have hqi : g ∈ quasiInvariantSubgroup (K := Multiplicative K) M ↔ g.toAdd ∈ h0Image :=
      (mem_quasiInvariantSubgroup_iff M g).trans (hMQ g)
    change g ∈ Set.range i ↔ g ∈ quasiInvariantSubgroup (K := Multiplicative K) M
    rw [hqi]
    rfl
  let r : H0 → Lp ℝ 2 M := fun h => root (orbit M (i (Multiplicative.ofAdd h)) : Measure _) M
  have he := rn_graph_embedding M i hi hinj hrange
  have he' : Topology.IsEmbedding (fun h : H0 => (h0Coordinates h, r h)) := he
  apply no_H0_invariant_hilbert_graph r he'
  intro h k t
  have hd := rn_distance_invariant M i hrange
    (Multiplicative.ofAdd t) (Multiplicative.ofAdd h) (Multiplicative.ofAdd k)
  change dist (r (t + h)) (r (t + k)) = dist (r h) (r k) at hd
  simpa only [add_comm t h, add_comm t k, dist_eq_norm] using hd

theorem c0_not_borel_reducible :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, RealNullRel x y ↔ EquivalentMeasures (f x : Measure Y) (f y : Measure Y) := by
  rintro ⟨f, hf, hred⟩
  exact c0_reduction_impossible f hf hred

theorem lp_reduction_impossible (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (f : (ℕ → ℝ) → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, RealLpRel p x y ↔
      EquivalentMeasures (f x : Measure Y) (f y : Measure Y)) : False := by
  let : PolishSpace (Multiplicative K) := inferInstanceAs (PolishSpace K)
  let := upgradeIsCompletelyMetrizable (Multiplicative K)
  let := baseTranslationAction K Y
  let := continuous_baseTranslationAction K Y
  have hpfin : p ≠ ⊤ := by intro h; norm_num [h] at hp
  let := hp_polish p hpfin
  let : PolishSpace (Multiplicative (Hp p)) := inferInstanceAs (PolishSpace (Hp p))
  let : MeasurableSpace (Multiplicative (Hp p)) := borel (Multiplicative (Hp p))
  let : BorelSpace (Multiplicative (Hp p)) := ⟨rfl⟩
  let F : K → ProbabilityMeasure Y := f ∘ realEmbed
  have hF : Measurable F := hf.comp continuous_realEmbed.measurable
  have hFred : ∀ x y, EquivalentMeasures (F x : Measure Y) (F y : Measure Y) ↔
      x - y ∈ hpImage p := by
    intro x y
    exact (hp_compose_reduction (fun μ ν : ProbabilityMeasure Y =>
      EquivalentMeasures (μ : Measure Y) (ν : Measure Y)) p (by linarith) f hred x y).symm
  obtain ⟨M, hM, hMQ⟩ := torus_polish_action_averaging (hpImage p) F hF hFred
  let := hM
  let i : Multiplicative (Hp p) →* Multiplicative K :=
    AddMonoidHom.toMultiplicative (hpInclusion p)
  have hi : Continuous i := hpInclusion_continuous p
  have hinj : Function.Injective i := hpInclusion_injective p
  have hrange : Set.range i = (quasiInvariantSubgroup (K := Multiplicative K) M : Set _) := by
    ext g
    have hqi : g ∈ quasiInvariantSubgroup (K := Multiplicative K) M ↔ g.toAdd ∈ hpImage p :=
      (mem_quasiInvariantSubgroup_iff M g).trans (hMQ g)
    change g ∈ Set.range i ↔ g ∈ quasiInvariantSubgroup (K := Multiplicative K) M
    rw [hqi]
    rfl
  let r : Hp p → Lp ℝ 2 M := fun h => root (orbit M (i (Multiplicative.ofAdd h)) : Measure _) M
  have he := rn_graph_embedding M i hi hinj hrange
  have he' : Topology.IsEmbedding (fun h : Hp p => (hpCoordinates p h, r h)) := he
  apply no_Hp_invariant_hilbert_graph p hp r he'
  intro h k t
  have hd := rn_distance_invariant M i hrange
    (Multiplicative.ofAdd t) (Multiplicative.ofAdd h) (Multiplicative.ofAdd k)
  change dist (r (t + h)) (r (t + k)) = dist (r h) (r k) at hd
  simpa only [add_comm t h, add_comm t k, dist_eq_norm] using hd

theorem lp_not_borel_reducible (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, RealLpRel p x y ↔ EquivalentMeasures (f x : Measure Y) (f y : Measure Y) := by
  rintro ⟨f, hf, hred⟩
  exact lp_reduction_impossible p hp f hf hred

/-- The negative statement with an ordinary finite real exponent and the
usual explicit summability definition, without ENNReal or lp notation. -/
theorem lp_summability_not_borel_reducible (p : ℝ) (hp : 2 < p) :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, (Summable fun n => |x n - y n| ^ p) ↔
        EquivalentMeasures (f x : Measure Y) (f y : Measure Y) := by
  have hp0 : 0 ≤ p := by linarith
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith⟩
  have hpt : 2 < (ENNReal.ofReal p).toReal := by simpa [ENNReal.toReal_ofReal hp0]
  rintro ⟨f, hf, hred⟩
  apply lp_reduction_impossible (ENNReal.ofReal p) hpt f hf
  intro x y
  simpa only [RealLpRel, memℓp_gen_iff (show 0 < (ENNReal.ofReal p).toReal by linarith),
    ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using hred x y

/-- The null-sequence statement written without auxiliary relation notation. -/
theorem null_difference_not_borel_reducible :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
        ((f x : Measure Y) ≪ f y ∧ (f y : Measure Y) ≪ f x) :=
  c0_not_borel_reducible

end MeasureEquivalenceNegative

#print axioms MeasureEquivalenceNegative.c0_reduction_impossible
#print axioms MeasureEquivalenceNegative.c0_not_borel_reducible
#print axioms MeasureEquivalenceNegative.lp_reduction_impossible
#print axioms MeasureEquivalenceNegative.lp_not_borel_reducible
#print axioms MeasureEquivalenceNegative.lp_summability_not_borel_reducible
#print axioms MeasureEquivalenceNegative.null_difference_not_borel_reducible
