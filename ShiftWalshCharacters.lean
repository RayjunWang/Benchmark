import ShiftBernoulliMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Data.Finset.SymmDiff

/-! Walsh characters on the actual fair free-group Bernoulli shift. These
are the concrete orthogonal coordinates for the remaining spectral-gap
argument. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators symmDiff

noncomputable section

namespace BenchmarkShift

local instance : DecidableEq Group := Classical.decEq Group

def coinSign (b : Bool) : ℝ := if b then 1 else -1

lemma abs_coinSign (b : Bool) : |coinSign b| = 1 := by cases b <;> norm_num [coinSign]
lemma coinSign_sq (b : Bool) : coinSign b ^ 2 = 1 := by cases b <;> norm_num [coinSign]

theorem continuous_coinSign : Continuous coinSign := continuous_of_discreteTopology

lemma integrable_coinSign : Integrable coinSign fairLaw :=
  Integrable.of_bound continuous_coinSign.measurable.aestronglyMeasurable 1
    (ae_of_all _ (fun b => by simp only [Real.norm_eq_abs, abs_coinSign, le_refl]))

lemma integral_coinSign : (∫ b, coinSign b ∂fairLaw) = 0 := by
  rw [integral_fintype integrable_coinSign]
  norm_num [Measure.real, fairLaw_singleton, coinSign]

def walsh (S : Finset Group) (x : Point) : ℝ := ∏ g ∈ S, coinSign (x g)

theorem continuous_walsh (S : Finset Group) : Continuous (walsh S) := by
  exact continuous_finsetProd S (fun g _ => continuous_coinSign.comp (continuous_apply g))

lemma abs_walsh (S : Finset Group) (x : Point) : |walsh S x| = 1 := by
  unfold walsh
  rw [Finset.abs_prod]
  simp only [abs_coinSign, Finset.prod_const_one]

lemma walsh_sq (S : Finset Group) (x : Point) : walsh S x ^ 2 = 1 := by
  unfold walsh
  rw [← Finset.prod_pow]
  simp only [coinSign_sq, Finset.prod_const_one]

lemma memLp_walsh (S : Finset Group) (p : ℝ≥0∞) : MemLp (walsh S) p bernoulli :=
  MemLp.of_bound (continuous_walsh S).measurable.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by simp only [Real.norm_eq_abs, abs_walsh, le_refl]))

lemma integral_walsh (S : Finset Group) : (∫ x, walsh S x ∂bernoulli) = if S = ∅ then 1 else 0 := by
  classical
  let f : (S → Bool) → ℝ := fun x => ∏ g : S, coinSign (x g)
  have hrep : walsh S = fun x => f (S.restrict x) := by
    funext x
    dsimp [walsh, f]
    exact (Finset.prod_attach S (fun g => coinSign (x g))).symm
  rw [hrep]
  have hf : AEStronglyMeasurable f (Measure.pi (fun _ : S => fairLaw)) :=
    (measurable_of_countable f).aestronglyMeasurable
  rw [show bernoulli = Measure.infinitePi (fun _ : Group => fairLaw) from rfl,
    integral_restrict_infinitePi (fun _ : Group => fairLaw) hf,
    integral_fintype_prod_eq_prod (fun _ : S => coinSign)]
  simp only [integral_coinSign]
  by_cases hS : S = ∅
  · subst S
    simp
  · rw [if_neg hS]
    obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨g, hg⟩) rfl

lemma walsh_mul (S T : Finset Group) (x : Point) :
    walsh S x * walsh T x = walsh (S ∆ T) x := by
  classical
  have hu : S ∪ T = (S ∆ T) ∪ (S ∩ T) := by
    ext g
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_symmDiff]
    tauto
  have hd : Disjoint (S ∆ T) (S ∩ T) := by
    rw [Finset.disjoint_left]
    intro g hg hboth
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at hg hboth
    tauto
  have hprod : walsh (S ∪ T) x = walsh (S ∆ T) x * walsh (S ∩ T) x := by
    unfold walsh
    rw [hu, Finset.prod_union hd]
  calc
    walsh S x * walsh T x = walsh (S ∪ T) x * walsh (S ∩ T) x :=
      (Finset.prod_union_inter (f := fun g => coinSign (x g))).symm
    _ = (walsh (S ∆ T) x * walsh (S ∩ T) x) * walsh (S ∩ T) x := by rw [hprod]
    _ = walsh (S ∆ T) x := by rw [mul_assoc, ← sq, walsh_sq, mul_one]

theorem integral_walsh_mul (S T : Finset Group) :
    (∫ x, walsh S x * walsh T x ∂bernoulli) = if S = T then 1 else 0 := by
  simp_rw [walsh_mul]
  rw [integral_walsh]
  simp only [Finset.symmDiff_eq_empty]

end BenchmarkShift

#print axioms BenchmarkShift.integral_walsh_mul
