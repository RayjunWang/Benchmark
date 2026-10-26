import CircleTopology
import CircleReduction

open Filter Topology Set TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCirclePresentation

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

def hpInclusion (p : ℝ≥0∞) : Hp p →+ K where
  toFun h := h
  map_zero' := rfl
  map_add' _ _ := rfl

lemma hpInclusion_injective (p : ℝ≥0∞) : Function.Injective (hpInclusion p) := by
  intro x y h
  apply lp.ext
  exact h

lemma hpInclusion_continuous (p : ℝ≥0∞) [Fact (1 ≤ p)] : Continuous (hpInclusion p) :=
  continuous_hp_coordinates p

def hpImage (p : ℝ≥0∞) : AddSubgroup K := (hpInclusion p).range

@[simp] lemma mem_hpImage_iff (p : ℝ≥0∞) (x : K) :
    x ∈ hpImage p ↔ Memℓp x p := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

def h0Inclusion : H0 →+ K where
  toFun h := (h : Hp ⊤)
  map_zero' := rfl
  map_add' _ _ := rfl

lemma h0Inclusion_injective : Function.Injective h0Inclusion := by
  intro x y h
  apply Subtype.ext
  apply lp.ext
  exact h

lemma h0Inclusion_continuous : Continuous h0Inclusion := continuous_h0_coordinates

def h0Image : AddSubgroup K := h0Inclusion.range

lemma memlp_top (x : K) : Memℓp x ⊤ := by
  apply memℓp_infty
  refine ⟨1 / 2, ?_⟩
  rintro a ⟨i, rfl⟩
  simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := x i) (by norm_num)

@[simp] lemma mem_h0Image_iff (x : K) :
    x ∈ h0Image ↔ Tendsto x atTop (𝓝 0) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.property
  · intro hx
    exact ⟨⟨⟨x, memlp_top x⟩, hx⟩, rfl⟩

open MeasureEquivalenceCircleReduction

theorem hp_coset_real_iff (p : ℝ≥0∞) (hp : 0 < p.toReal) (x y : K) :
    x - y ∈ hpImage p ↔ RealLpRel p (realEmbed x) (realEmbed y) := by
  rw [mem_hpImage_iff]
  exact circle_real_lp_reduction p hp x y

theorem h0_coset_real_iff (x y : K) :
    x - y ∈ h0Image ↔ RealNullRel (realEmbed x) (realEmbed y) := by
  rw [mem_h0Image_iff]
  exact circle_real_null_reduction x y

theorem hp_compose_reduction {Y : Type*} (R : Y → Y → Prop)
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (f : (ℕ → ℝ) → Y)
    (hf : ∀ x y, RealLpRel p x y ↔ R (f x) (f y)) (x y : K) :
    x - y ∈ hpImage p ↔ R (f (realEmbed x)) (f (realEmbed y)) :=
  (hp_coset_real_iff p hp x y).trans (hf _ _)

theorem h0_compose_reduction {Y : Type*} (R : Y → Y → Prop)
    (f : (ℕ → ℝ) → Y)
    (hf : ∀ x y, RealNullRel x y ↔ R (f x) (f y)) (x y : K) :
    x - y ∈ h0Image ↔ R (f (realEmbed x)) (f (realEmbed y)) :=
  (h0_coset_real_iff x y).trans (hf _ _)

end MeasureEquivalenceCirclePresentation

#print axioms MeasureEquivalenceCirclePresentation.mem_hpImage_iff
#print axioms MeasureEquivalenceCirclePresentation.mem_h0Image_iff
#print axioms MeasureEquivalenceCirclePresentation.hpInclusion_continuous
#print axioms MeasureEquivalenceCirclePresentation.h0Inclusion_continuous
#print axioms MeasureEquivalenceCirclePresentation.hp_compose_reduction
#print axioms MeasureEquivalenceCirclePresentation.h0_compose_reduction
