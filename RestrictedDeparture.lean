import RestrictedDensity
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def departureSet (u : ℝ) : Set ℝ := {t | t ∈ baseInterval ∧ t + u ∉ baseInterval}
def departureProbability (u : ℝ) : ℝ≥0∞ := baseMeasure (departureSet u)

theorem measurable_departureSet (u : ℝ) : MeasurableSet (departureSet u) :=
  (show MeasurableSet baseInterval from measurableSet_Icc).inter
    ((measurable_id.add_const u) (show MeasurableSet baseInterval from measurableSet_Icc)).compl

theorem exponentialDensity_le_two {t : ℝ} (ht : t ∈ baseInterval) :
    exponentialDensity t ≤ 2 := by
  have hle : Real.exp (-t) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith [ht.1])
  simpa [exponentialDensity] using ENNReal.ofReal_le_ofReal hle

theorem one_le_exponentialDensity {t : ℝ} (ht : t ∈ baseInterval) :
    (1 : ℝ≥0∞) ≤ exponentialDensity t := by
  have hle : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (neg_nonneg.mpr ht.2)
  exact_mod_cast ENNReal.ofReal_le_ofReal hle

theorem baseMeasure_le_two_volume : baseMeasure ≤ (2 : ℝ≥0∞) • (volume : Measure ℝ) := by
  have hle : baseMeasure ≤ (2 : ℝ≥0∞) • (volume.restrict baseInterval) := by
    unfold baseMeasure exponentialMeasure
    rw [restrict_withDensity (show MeasurableSet baseInterval from measurableSet_Icc)]
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc)] with t ht
    exact exponentialDensity_le_two ht
  apply hle.trans
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left' (Measure.restrict_le_self s) 2

theorem volume_restrict_le_baseMeasure : (volume : Measure ℝ).restrict baseInterval ≤ baseMeasure := by
  unfold baseMeasure exponentialMeasure
  rw [restrict_withDensity (show MeasurableSet baseInterval from measurableSet_Icc)]
  conv_lhs => rw [← withDensity_one (μ := volume.restrict baseInterval)]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc)] with t ht
  exact one_le_exponentialDensity ht

theorem departureProbability_le (u : ℝ) :
    departureProbability u ≤ 2 * ENNReal.ofReal |u| := by
  have hρ := baseMeasure_le_two_volume (departureSet u)
  change departureProbability u ≤ _ at hρ
  simp only [Measure.smul_apply, smul_eq_mul] at hρ
  by_cases hu : 0 ≤ u
  · have hsub : departureSet u ⊆ Ioc (-u) 0 := by
      intro t ht
      have htl : -Real.log 2 ≤ t := ht.1.1
      have htr : t ≤ 0 := ht.1.2
      have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
      have hpos : 0 < t + u := by by_contra h; apply hbad; constructor <;> linarith
      constructor <;> linarith
    exact hρ.trans ((mul_le_mul_left' (measure_mono hsub) 2).trans_eq (by
      rw [Real.volume_Ioc]
      simp [abs_of_nonneg hu]))
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hsub : departureSet u ⊆ Ico (-Real.log 2) (-Real.log 2 - u) := by
      intro t ht
      have htl : -Real.log 2 ≤ t := ht.1.1
      have htr : t ≤ 0 := ht.1.2
      have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
      have hneg : t + u < -Real.log 2 := by by_contra h; apply hbad; constructor <;> linarith
      constructor <;> linarith
    exact hρ.trans ((mul_le_mul_left' (measure_mono hsub) 2).trans_eq (by
      rw [Real.volume_Ico]
      rw [show (-Real.log 2 - u) - -Real.log 2 = -u by ring, abs_of_nonpos hu']))

theorem departureSet_of_nonneg (u : ℝ) (hu : 0 ≤ u) (huL : u ≤ Real.log 2) :
    departureSet u = Ioc (-u) 0 := by
  ext t
  constructor
  · intro ht
    have htl : -Real.log 2 ≤ t := ht.1.1
    have htr : t ≤ 0 := ht.1.2
    have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
    constructor
    · by_contra h
      apply hbad
      constructor <;> linarith
    · exact htr
  · rintro ⟨htl, htr⟩
    constructor
    · constructor <;> linarith
    · intro hbad
      have := hbad.2
      linarith

theorem departureSet_of_nonpos (u : ℝ) (hu : u ≤ 0) (huL : -u ≤ Real.log 2) :
    departureSet u = Ico (-Real.log 2) (-Real.log 2 - u) := by
  ext t
  constructor
  · intro ht
    have htl : -Real.log 2 ≤ t := ht.1.1
    have htr : t ≤ 0 := ht.1.2
    have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
    constructor
    · exact htl
    · by_contra h
      apply hbad
      constructor <;> linarith
  · rintro ⟨htl, htr⟩
    constructor
    · constructor <;> linarith
    · intro hbad
      have := hbad.1
      linarith

theorem departureProbability_ge_abs_of_small (u : ℝ) (huL : |u| ≤ Real.log 2) :
    ENNReal.ofReal |u| ≤ departureProbability u := by
  change ENNReal.ofReal |u| ≤ baseMeasure (departureSet u)
  have hle := volume_restrict_le_baseMeasure (departureSet u)
  rw [Measure.restrict_apply (measurable_departureSet u),
    Set.inter_eq_left.mpr (show departureSet u ⊆ baseInterval from fun _ h => h.1)] at hle
  by_cases hu : 0 ≤ u
  · have he := departureSet_of_nonneg u hu (by simpa [abs_of_nonneg hu] using huL)
    rw [he, Real.volume_Ioc] at hle
    rw [he]
    simpa [abs_of_nonneg hu] using hle
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have he := departureSet_of_nonpos u hu' (by simpa [abs_of_nonpos hu'] using huL)
    rw [he, Real.volume_Ico] at hle
    rw [he]
    simpa [abs_of_nonpos hu', show (-Real.log 2 - u) - -Real.log 2 = -u by ring] using hle

theorem departureProbability_eq_one_of_large (u : ℝ) (huL : Real.log 2 ≤ |u|) :
    departureProbability u = 1 := by
  have ha : ∀ᵐ t ∂baseMeasure, t ∈ departureSet u := by
    filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc),
      Measure.ae_ne baseMeasure (-Real.log 2), Measure.ae_ne baseMeasure (0 : ℝ)] with t ht htl htr
    refine ⟨ht, ?_⟩
    intro hbad
    by_cases hu : 0 ≤ u
    · have hshift : Real.log 2 ≤ u := by simpa [abs_of_nonneg hu] using huL
      apply htl
      have h1 : -Real.log 2 ≤ t := ht.1
      have h2 : t + u ≤ 0 := hbad.2
      linarith
    · have hshift : Real.log 2 ≤ -u := by simpa [abs_of_nonpos (le_of_not_ge hu)] using huL
      apply htr
      have h1 : t ≤ 0 := ht.2
      have h2 : -Real.log 2 ≤ t + u := hbad.1
      linarith
  have hc : baseMeasure (departureSet u)ᶜ = 0 := ha
  have he := measure_add_measure_compl (μ := baseMeasure) (measurable_departureSet u)
  rw [hc, add_zero, measure_univ] at he
  exact he

theorem departureProbability_lower (u : ℝ) :
    ENNReal.ofReal (min 1 |u|) ≤ departureProbability u := by
  by_cases hu : |u| ≤ Real.log 2
  · exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
      (departureProbability_ge_abs_of_small u hu)
  · rw [departureProbability_eq_one_of_large u (le_of_not_ge hu)]
    simpa using ENNReal.ofReal_le_ofReal (min_le_left (1 : ℝ) |u|)

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.departureProbability_le
#print axioms MeasureEquivalenceRestrictedProduct.departureProbability_lower
