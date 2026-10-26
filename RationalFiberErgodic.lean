import DenseEventErgodic
import RestrictedDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Rat

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem finite_real_aeconst_of_rational_invariant (n : ℕ)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin n → ℚ,
      (fun x : Fin n → ℝ => x + fun i => (q i : ℝ)) ⁻¹' E =ᵐ[volume] E) :
    EventuallyConst E (ae (volume : Measure (Fin n → ℝ))) := by
  let f : (Fin n → ℚ) → (Fin n → ℝ) := fun q i => (q i : ℝ)
  have hd : DenseRange f := DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast)
  apply aeconst_of_dense_translation_invariant volume (range f) hd E hE
  rintro q ⟨r, rfl⟩
  exact hinv r

def sumTailEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) where
  toFun x := (∑ i, x i, fun i => x i.succ)
  invFun z := Fin.cons (z.1 - ∑ i, z.2 i) z.2
  left_inv := by
    intro x
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Fin.sum_univ_succ]
      ring
    · simp
  right_inv := by
    rintro ⟨s, y⟩
    apply Prod.ext
    · simp [Fin.sum_univ_succ]
    · rfl
  measurable_toFun := by
    change Measurable (fun x : Fin (n + 1) → ℝ => (∑ i, x i, fun i : Fin n => x i.succ))
    fun_prop
  measurable_invFun := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Measurable (fun z : ℝ × (Fin n → ℝ) => z.1 - ∑ i, z.2 i)
      fun_prop
    · exact (measurable_pi_apply j).comp measurable_snd

theorem measurePreserving_sumTailEquiv (n : ℕ) :
    MeasurePreserving (sumTailEquiv n) (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let shear : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) := fun z =>
    (z.1, z.2 + ∑ i, z.1 i)
  have hsplit : MeasurePreserving split (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hs1 : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) := Measure.measurePreserving_swap
  have hs2 : MeasurePreserving Prod.swap
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := Measure.measurePreserving_swap
  have hshear : MeasurePreserving shear
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure (Fin n → ℝ))).skew_product
      (g := fun y t => t + ∑ i, y i) (by fun_prop)
      (ae_of_all _ (fun y => map_add_right_eq_self volume (∑ i, y i)))
  have hc := hs2.comp (hshear.comp (hs1.comp hsplit))
  have he : (Prod.swap ∘ shear ∘ Prod.swap ∘ split) = sumTailEquiv n := by
    funext x
    apply Prod.ext
    · simp [Function.comp_def, shear, split, sumTailEquiv,
        MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ, Fin.tail]
    · simp [Function.comp_def, shear, split, sumTailEquiv,
        MeasurableEquiv.piFinSuccAbove, Fin.tail]
      rfl
  rw [he] at hc
  exact hc

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.finite_real_aeconst_of_rational_invariant
#print axioms MeasureEquivalenceRestrictedProduct.measurePreserving_sumTailEquiv
