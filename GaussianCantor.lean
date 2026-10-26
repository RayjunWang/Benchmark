import GaussianCanonical
import SnowflakeReduction
import Mathlib.Data.Rat.Encodable

/-! A concrete rational-cut Cantor encoding of the Gaussian family. The encoding
is only Borel, but its restriction by pushforward to this family is weakly continuous.
All probability measurability statements use the canonical evaluation structure.
-/

open MeasureTheory ProbabilityTheory Filter Set BoundedContinuousFunction
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceGaussianCantor

open MeasureEquivalenceGaussian

abbrev CutCantor := (ℕ × ℚ) → Fin 2

local instance : Denumerable ℚ := Denumerable.ofEncodableOfInfinite ℚ

example : DiscreteTopology (Fin 2) := inferInstance
instance finTwo_polish : PolishSpace (Fin 2) :=
  (show Continuous (fun i : Fin 2 => (i : ℕ)) from continuous_of_discreteTopology).isClosedEmbedding
    Fin.val_injective |>.polishSpace

example : CompactSpace CutCantor := inferInstance
instance cutCantor_polish : PolishSpace CutCantor := inferInstance
example : BorelSpace CutCantor := inferInstance

/-- The countable rational-coordinate product is the usual binary Cantor product. -/
def cutCantorHomeomorphNat : CutCantor ≃ₜ (ℕ → Fin 2) :=
  Homeomorph.piCongrLeft (Y := fun _ => Fin 2) (Denumerable.eqv (ℕ × ℚ))

def cutEncode (x : ℕ → ℝ) : CutCantor :=
  fun i => if (i.2 : ℝ) < x i.1 then 1 else 0

theorem measurable_cutEncode : Measurable cutEncode := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i.1))
    measurable_const measurable_const

theorem injective_cutEncode : Function.Injective cutEncode := by
  intro x y h
  funext n
  apply le_antisymm
  · by_contra hle
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn (lt_of_not_ge hle)
    have he := congrFun h (n, q)
    simp only [cutEncode, if_pos hqx, if_neg (not_lt.mpr hyq.le)] at he
    norm_num at he
  · by_contra hle
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn (lt_of_not_ge hle)
    have he := congrFun h (n, q)
    simp only [cutEncode, if_pos hqy, if_neg (not_lt.mpr hxq.le)] at he
    norm_num at he

theorem measurableEmbedding_cutEncode : MeasurableEmbedding cutEncode :=
  measurable_cutEncode.measurableEmbedding injective_cutEncode

def cutGaussian (a : ℕ → ℝ) : ProbabilityMeasure CutCantor :=
  ⟨(gaussianProduct a).map cutEncode,
    (gaussianProduct a).isProbabilityMeasure_map measurable_cutEncode.aemeasurable⟩

theorem measurable_cutGaussian : Measurable cutGaussian :=
  ((Measure.measurable_map cutEncode measurable_cutEncode).comp
    measurable_gaussianProduct_canonical).subtype_mk

theorem cut_map_ac_iff (μ ν : Measure (ℕ → ℝ)) :
    μ.map cutEncode ≪ ν.map cutEncode ↔ μ ≪ ν := by
  constructor
  · intro h s hs
    have hz : (ν.map cutEncode) (cutEncode '' s) = 0 := by
      rw [measurableEmbedding_cutEncode.map_apply,
        injective_cutEncode.preimage_image, hs]
    have hh := h hz
    rwa [measurableEmbedding_cutEncode.map_apply,
      injective_cutEncode.preimage_image] at hh
  · exact measurableEmbedding_cutEncode.absolutelyContinuous_map

theorem cutGaussian_mutualAC_iff (a b : ℕ → ℝ) :
    ((cutGaussian a : Measure CutCantor) ≪ cutGaussian b ∧
      (cutGaussian b : Measure CutCantor) ≪ cutGaussian a) ↔
      Summable (fun n => (a n - b n) ^ 2) := by
  change ((gaussianProduct a).map cutEncode ≪ (gaussianProduct b).map cutEncode ∧
    (gaussianProduct b).map cutEncode ≪ (gaussianProduct a).map cutEncode) ↔ _
  rw [cut_map_ac_iff, cut_map_ac_iff]
  exact gaussian_mutualAC_iff_summable a b

theorem continuousAt_cutEncode {z : ℕ → ℝ}
    (hz : ∀ i : ℕ × ℚ, z i.1 ≠ (i.2 : ℝ)) : ContinuousAt cutEncode z := by
  apply continuousAt_pi.2
  intro i
  by_cases hi : (i.2 : ℝ) < z i.1
  · have he : ∀ᶠ x : ℕ → ℝ in 𝓝 z, (i.2 : ℝ) < x i.1 :=
      (isOpen_lt continuous_const (continuous_apply i.1)).mem_nhds hi
    apply (show ContinuousAt (fun _ : ℕ → ℝ => (1 : Fin 2)) z from continuousAt_const).congr
    filter_upwards [he] with x hx
    simp [cutEncode, hx]
  · have hi' : z i.1 < (i.2 : ℝ) := lt_of_le_of_ne (le_of_not_gt hi) (hz i)
    have he : ∀ᶠ x : ℕ → ℝ in 𝓝 z, x i.1 < (i.2 : ℝ) :=
      (isOpen_lt (continuous_apply i.1) continuous_const).mem_nhds hi'
    apply (show ContinuousAt (fun _ : ℕ → ℝ => (0 : Fin 2)) z from continuousAt_const).congr
    filter_upwards [he] with x hx
    simp [cutEncode, not_lt.mpr hx.le]

theorem ae_avoid_rational_cuts (a : ℕ → ℝ) :
    ∀ᵐ x ∂gaussianProduct 0, ∀ i : ℕ × ℚ, (x + a) i.1 ≠ (i.2 : ℝ) := by
  rw [ae_all_iff]
  intro i
  have hmap : (gaussianProduct 0).map (fun x => x i.1) = gaussianReal 0 1 := by
    exact Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) i.1
  let : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hne : ∀ᵐ t ∂gaussianReal 0 1, t ≠ (i.2 : ℝ) - a i.1 := by
    exact Measure.ae_ne _ _
  rw [← hmap] at hne
  have hpull := (ae_map_iff (measurable_pi_apply i.1).aemeasurable
    (measurableSet_singleton ((i.2 : ℝ) - a i.1)).compl).1 hne
  filter_upwards [hpull] with x hx
  simp only [Pi.add_apply]
  exact fun he => hx (by linarith)

theorem integral_cutGaussian (a : ℕ → ℝ) (f : CutCantor →ᵇ ℝ) :
    (∫ x, f x ∂cutGaussian a) =
      ∫ x, f (cutEncode (x + a)) ∂gaussianProduct 0 := by
  change (∫ x, f x ∂(gaussianProduct a).map cutEncode) = _
  rw [integral_map measurable_cutEncode.aemeasurable f.continuous.aestronglyMeasurable]
  have hm := gaussianProduct_map_add a 0
  simp only [zero_add] at hm
  rw [← hm]
  exact integral_map (continuous_id.add_const a).measurable.aemeasurable
    (f.continuous.measurable.comp measurable_cutEncode).aestronglyMeasurable

theorem continuous_cutGaussian : Continuous cutGaussian := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_cutGaussian]
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun b =>
      (f.continuous.measurable.comp
        (measurable_cutEncode.comp (measurable_id.add_const b))).aestronglyMeasurable)
  · exact ⟨‖f‖, Eventually.of_forall (fun b => ae_of_all _ (fun x => f.norm_coe_le_norm _))⟩
  · filter_upwards [ae_avoid_rational_cuts a] with x hx
    exact f.continuous.continuousAt.comp
      ((continuousAt_cutEncode hx).comp (continuous_const.add continuous_id).continuousAt)

theorem exists_continuous_cantor_reduction (p : ℝ) (hp0 : 0 < p) (hp2 : p ≤ 2) :
    ∃ G : (ℕ → ℝ) → ProbabilityMeasure CutCantor, Continuous G ∧ Measurable G ∧
      ∀ x y : ℕ → ℝ, Summable (fun n => |x n - y n| ^ p) ↔
        ((G x : Measure CutCantor) ≪ G y ∧ (G y : Measure CutCantor) ≪ G x) := by
  by_cases hp : p = 2
  · subst p
    refine ⟨cutGaussian, continuous_cutGaussian, measurable_cutGaussian, ?_⟩
    intro x y
    simpa only [Real.rpow_two, sq_abs] using (cutGaussian_mutualAC_iff x y).symm
  · obtain ⟨R, hR, hiff⟩ := MeasureEquivalenceSnowflake.exists_continuous_reduction_to_square
      p hp0 (lt_of_le_of_ne hp2 hp)
    refine ⟨fun x => cutGaussian (R x), continuous_cutGaussian.comp hR,
      measurable_cutGaussian.comp hR.measurable, ?_⟩
    intro x y
    exact (hiff x y).trans (cutGaussian_mutualAC_iff (R x) (R y)).symm

theorem exists_continuous_cantor_reduction_one_le (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ G : (ℕ → ℝ) → ProbabilityMeasure CutCantor, Continuous G ∧ Measurable G ∧
      ∀ x y : ℕ → ℝ, Summable (fun n => |x n - y n| ^ p) ↔
        ((G x : Measure CutCantor) ≪ G y ∧ (G y : Measure CutCantor) ≪ G x) :=
  exists_continuous_cantor_reduction p (lt_of_lt_of_le zero_lt_one hp1) hp2

#print axioms measurableEmbedding_cutEncode
#print axioms continuous_cutGaussian
#print axioms exists_continuous_cantor_reduction
#print axioms exists_continuous_cantor_reduction_one_le

end MeasureEquivalenceGaussianCantor
