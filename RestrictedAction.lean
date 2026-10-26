import RestrictedModulus
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def rationalTotal : (ℕ →₀ ℚ) →+ ℚ :=
  Finsupp.liftAddHom (fun _ : ℕ => AddMonoidHom.id ℚ)

theorem rationalTotal_eq_sum (q : ℕ →₀ ℚ) :
    rationalTotal q = q.sum (fun _ a => a) := by
  exact Finsupp.liftAddHom_apply _ _

def rationalZeroSumGroup : AddSubgroup (ℕ →₀ ℚ) := rationalTotal.ker

def rationalRealShift : (ℕ →₀ ℚ) →+ RealSequences where
  toFun q k := (q k : ℝ)
  map_zero' := by funext k; simp
  map_add' := by intro q r; funext k; simp

theorem rationalRealShift_injective : Function.Injective rationalRealShift := by
  intro q r h
  ext k
  exact Rat.cast_injective (congrFun h k)

theorem summable_abs_rationalRealShift (q : ℕ →₀ ℚ) :
    Summable (fun k => |rationalRealShift q k|) := by
  exact summable_of_hasFiniteSupport
    (q.hasFiniteSupport.fun_comp (g := fun a : ℚ => |(a : ℝ)|) (by simp))

theorem tsum_rationalRealShift (q : ℕ →₀ ℚ) :
    (∑' k, rationalRealShift q k) = (rationalTotal q : ℝ) := by
  rw [tsum_eq_sum (s := q.support) (fun k hk => by
    change (q k : ℝ) = 0
    rw [Finsupp.notMem_support_iff.mp hk, Rat.cast_zero])]
  rw [rationalTotal_eq_sum]
  change (∑ k ∈ q.support, (q k : ℝ)) = ((∑ k ∈ q.support, q k : ℚ) : ℝ)
  norm_cast

def rationalTranslation (q : rationalZeroSumGroup) (x : RealSequences) : RealSequences :=
  x + rationalRealShift q

theorem measurePreserving_rationalTranslation (q : rationalZeroSumGroup) :
    MeasurePreserving (rationalTranslation q) restrictedProductMeasure restrictedProductMeasure := by
  constructor
  · exact measurable_id.add_const _
  · have he := map_summable_restrictedProductMeasure (rationalRealShift q)
      (summable_abs_rationalRealShift q)
    rw [tsum_rationalRealShift, show rationalTotal (q : ℕ →₀ ℚ) = 0 from q.property,
      Rat.cast_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at he
    exact he

theorem rationalTranslation_free (q : rationalZeroSumGroup) (x : RealSequences) :
    rationalTranslation q x = x ↔ q = 0 := by
  constructor
  · intro h
    have hz : rationalRealShift (q : ℕ →₀ ℚ) = 0 := by
      exact add_left_cancel (show x + rationalRealShift q = x + 0 from by
        simpa only [rationalTranslation, add_zero] using h)
    apply Subtype.ext
    apply rationalRealShift_injective
    simpa using hz
  · rintro rfl
    simp [rationalTranslation]

theorem rationalZeroSum_countable : Countable rationalZeroSumGroup := inferInstance

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.measurePreserving_rationalTranslation
#print axioms MeasureEquivalenceRestrictedProduct.rationalTranslation_free
