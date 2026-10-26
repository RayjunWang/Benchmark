import RestrictedFiniteEvent
import RestrictedZeroOne

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def finBlockSwapFun (M : ℕ) (i : Fin (2 * M + 1)) : Fin (2 * M + 1) :=
  ⟨blockSwap M i, by
    have hi := i.isLt
    change blockSwapFun M i < 2 * M + 1
    unfold blockSwapFun
    split_ifs <;> omega⟩

theorem finBlockSwapFun_involutive (M : ℕ) : Function.Involutive (finBlockSwapFun M) := by
  intro i
  apply Fin.ext
  exact blockSwap_involutive M i

def finBlockSwap (M : ℕ) : Equiv.Perm (Fin (2 * M + 1)) where
  toFun := finBlockSwapFun M
  invFun := finBlockSwapFun M
  left_inv := finBlockSwapFun_involutive M
  right_inv := finBlockSwapFun_involutive M

theorem headTail_blockSwap (M : ℕ) (x : RealSequences) :
    headTailEquiv (2 * M + 1) (permute (blockSwap M) x) =
      (fun i => (headTailEquiv (2 * M + 1) x).1 (finBlockSwap M i),
        (headTailEquiv (2 * M + 1) x).2) := by
  apply Prod.ext
  · rfl
  · funext k
    change x (blockSwap M (2 * M + 1 + k)) = x (2 * M + 1 + k)
    rw [blockSwap_large M _ (by omega)]

theorem blockSwap_base_invariant_of_rational_invariant
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E) (M : ℕ) :
    (permute (blockSwap M)) ⁻¹' E =ᵐ[tailProbability] E := by
  let N := 2 * M + 1
  let F := (headTailEquiv N).symm ⁻¹' E
  have hF : MeasurableSet F := (headTailEquiv N).symm.measurable hE
  have hp := finite_permutation_invariant_of_zeroSum_invariant tailProbability (2 * M)
    F hF (head_event_zeroSum_invariant N E hE hinv) (finBlockSwap M)
  have hp' := ((finite_exponential_ac_volume N).prod Measure.AbsolutelyContinuous.rfl).ae_eq hp
  have hm : MeasurePreserving (headTailEquiv N).symm
      ((Measure.pi (fun _ : Fin N => exponentialMeasure)).prod tailProbability) (stageMeasure N) :=
    ⟨(headTailEquiv N).symm.measurable, rfl⟩
  have hh := (hm.symm (headTailEquiv N).symm).quasiMeasurePreserving.ae_eq hp'
  have hs : (permute (blockSwap M)) ⁻¹' E =ᵐ[stageMeasure N] E := by
    filter_upwards [hh] with x hx
    change E ((headTailEquiv N).symm
      ((fun i => (headTailEquiv N x).1 (finBlockSwap M i)), (headTailEquiv N x).2)) =
        E ((headTailEquiv N).symm (headTailEquiv N x)) at hx
    rw [← headTail_blockSwap M x, MeasurableEquiv.symm_apply_apply,
      MeasurableEquiv.symm_apply_apply] at hx
    exact hx
  have hbase : tailProbability ≪ stageMeasure N := by
    rw [← stageMeasure_restrict_base N]
    exact Measure.restrict_le_self.absolutelyContinuous
  exact hbase.ae_eq hs

theorem rationalZeroSum_ergodic
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E) :
    restrictedProductMeasure E = 0 ∨ restrictedProductMeasure Eᶜ = 0 := by
  apply null_or_conull_of_invariant_and_base_zero_one E hE hinv
  apply tailProbability_zero_one_of_blockSwap_invariant E hE
  exact blockSwap_base_invariant_of_rational_invariant E hE hinv

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.rationalZeroSum_ergodic
