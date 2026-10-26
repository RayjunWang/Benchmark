import FiberMultiplicityMatching
import PiecewiseMeasureTransport

/-! Equal multiplicities give an actual measure-preserving fiber
transport and hence a genuine base-module unitary. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceEquidecomposition

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberRestrictedMeasure_apply (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (s : Set (X × ℕ)) (hs : MeasurableSet s) :
    fiberRestrictedMeasure μ A s =
      ∫⁻ x, ∑' i : ℕ, if x ∈ A i ∧ (x,i) ∈ s then (1 : ℝ≥0∞) else 0 ∂μ := by
  classical
  have hFA := measureFiberSet_measurable A hA
  calc
    fiberRestrictedMeasure μ A s = fiberAmbientMeasure μ (s ∩ measureFiberSet A) :=
      Measure.restrict_apply hs
    _ = ∫⁻ p, (s ∩ measureFiberSet A).indicator (fun _ => (1 : ℝ≥0∞)) p ∂fiberAmbientMeasure μ := by
      simp only [lintegral_indicator (hs.inter hFA), lintegral_one, Measure.restrict_apply_univ]
    _ = ∫⁻ x, ∫⁻ i : ℕ, (s ∩ measureFiberSet A).indicator (fun _ => (1 : ℝ≥0∞)) (x,i)
        ∂Measure.count ∂μ :=
      lintegral_prod _ (measurable_const.indicator (hs.inter hFA)).aemeasurable
    _ = _ := by
      congr 1
      funext x
      rw [lintegral_count]
      apply tsum_congr
      intro i
      by_cases ha : x ∈ A i <;> by_cases hsi : (x,i) ∈ s <;>
        simp [measureFiberSet,ha,hsi]

theorem fiberNthMatch_preserving (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B) :
    MeasurePreserving (fiberNthMatch A B) (fiberRestrictedMeasure μ A) (fiberRestrictedMeasure μ B) := by
  classical
  refine ⟨fiberNthMatch_measurable A B hA hB, ?_⟩
  ext s hs
  rw [Measure.map_apply (fiberNthMatch_measurable A B hA hB) hs,
    fiberRestrictedMeasure_apply μ A hA _ ((fiberNthMatch_measurable A B hA hB) hs),
    fiberRestrictedMeasure_apply μ B hB s hs]
  apply lintegral_congr_ae
  filter_upwards [hcard] with x hx
  let E := fiberActiveEquiv A B x hx
  change (∑' i : ℕ, if x ∈ A i ∧ fiberNthMatch A B (x,i) ∈ s then (1 : ℝ≥0∞) else 0) =
    ∑' j : ℕ, if x ∈ B j ∧ (x,j) ∈ s then (1 : ℝ≥0∞) else 0
  calc
    (∑' i : ℕ, if x ∈ A i ∧ fiberNthMatch A B (x,i) ∈ s then (1 : ℝ≥0∞) else 0) =
        ∑' i : {i : ℕ | x ∈ A i}, if fiberNthMatch A B (x,i.val) ∈ s then (1 : ℝ≥0∞) else 0 := by
      rw [tsum_subtype {i : ℕ | x ∈ A i}
        (fun i : ℕ => if fiberNthMatch A B (x,i) ∈ s then (1 : ℝ≥0∞) else 0)]
      apply tsum_congr
      intro i
      by_cases hi : x ∈ A i <;> simp [hi]
    _ = ∑' j : {j : ℕ | x ∈ B j}, if (x,j.val) ∈ s then (1 : ℝ≥0∞) else 0 :=
      E.tsum_eq (fun j : {j : ℕ | x ∈ B j} => if (x,j.val) ∈ s then (1 : ℝ≥0∞) else 0)
    _ = ∑' j : ℕ, if x ∈ B j ∧ (x,j) ∈ s then (1 : ℝ≥0∞) else 0 := by
      rw [tsum_subtype {j : ℕ | x ∈ B j}
        (fun j : ℕ => if (x,j) ∈ s then (1 : ℝ≥0∞) else 0)]
      apply tsum_congr
      intro j
      by_cases hj : x ∈ B j <;> simp [hj]

theorem fiberNthMatch_inverse_ae (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B) :
    ∀ᵐ p ∂fiberRestrictedMeasure μ A, fiberNthMatch B A (fiberNthMatch A B p) = p := by
  have hbase := (Measure.quasiMeasurePreserving_fst
    (μ := μ) (ν := (Measure.count : Measure ℕ))).ae hcard
  filter_upwards [ae_restrict_of_ae hbase, ae_restrict_mem (measureFiberSet_measurable A hA)]
    with p hp hA'
  exact fiberNthMatch_inverse A B p.1 hp p.2 hA'

def fiberMultiplicityUnitary (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B) :
    Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B) :=
  pullbackUnitary (fiberRestrictedMeasure μ B) (fiberRestrictedMeasure μ A)
    (fiberNthMatch B A) (fiberNthMatch A B)
    (fiberNthMatch_preserving μ B A hB hA hcard.symm)
    (fiberNthMatch_preserving μ A B hA hB hcard)
    (fiberNthMatch_inverse_ae μ B A hB hcard.symm)

theorem fiberMultiplicityUnitary_coe (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B)
    (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    fiberMultiplicityUnitary μ A B hA hB hcard f =ᵐ[fiberRestrictedMeasure μ B]
      fun p => f (fiberNthMatch B A p) :=
  Lp.coeFn_compMeasurePreserving f (fiberNthMatch_preserving μ B A hB hA hcard.symm)

theorem fiberMultiplicityUnitary_intertwines_projections (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    fiberMultiplicityUnitary μ A B hA hB hcard
      (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
      indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst)
        (fiberMultiplicityUnitary μ A B hA hB hcard f) := by
  apply Lp.ext
  filter_upwards [fiberMultiplicityUnitary_coe μ A B hA hB hcard
      (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f),
    (fiberNthMatch_preserving μ B A hB hA hcard.symm).quasiMeasurePreserving.ae
      (indicatorL2_coe (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f),
    indicatorL2_coe (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst)
      (fiberMultiplicityUnitary μ A B hA hB hcard f),
    fiberMultiplicityUnitary_coe μ A B hA hB hcard f] with p hleft hin hright hf
  rw [hleft, hin, hright]
  by_cases hp : p.1 ∈ s <;> simp [hp,hf,fiberNthMatch_fst]

end
end MeasureUnitary

#print axioms MeasureUnitary.fiberNthMatch_preserving
#print axioms MeasureUnitary.fiberMultiplicityUnitary_intertwines_projections
