import CouplingMarkov
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub

/-! Explicit stationary couplings from overlap measures along a
measurable automorphism. Their edges detect invariance. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

/-- The bounded acceptance flow is the overlap of μ and its translate. -/
noncomputable def acceptanceFlow (μ : Measure Z) (e : Z ≃ᵐ Z) : Measure Z :=
  μ.withDensity (fun z => min 1 ((μ.map e).rnDeriv μ z))

theorem acceptanceFlow_le (μ : Measure Z) (e : Z ≃ᵐ Z) : acceptanceFlow μ e ≤ μ := by
  calc
    _ ≤ μ.withDensity 1 := withDensity_mono (Eventually.of_forall (fun z => min_le_left _ _))
    _ = μ := withDensity_one

instance acceptanceFlow_finite (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z) :
    IsFiniteMeasure (acceptanceFlow μ e) := isFiniteMeasure_of_le μ (acceptanceFlow_le μ e)

theorem acceptanceFlow_le_map (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z)
    (h : μ.map e ≪ μ) : acceptanceFlow μ e ≤ μ.map e := by
  calc
    _ ≤ μ.withDensity ((μ.map e).rnDeriv μ) :=
      withDensity_mono (Eventually.of_forall (fun z => min_le_right _ _))
    _ = μ.map e := Measure.withDensity_rnDeriv_eq _ _ h

theorem acceptanceFlow_equivalent (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z)
    (h : μ ≪ μ.map e) : μ ≪ acceptanceFlow μ e ∧ acceptanceFlow μ e ≪ μ := by
  constructor
  · apply withDensity_absolutelyContinuous'
    · exact (measurable_const.min (Measure.measurable_rnDeriv _ _)).aemeasurable
    · filter_upwards [Measure.rnDeriv_pos' h] with z hz
      exact (lt_min zero_lt_one hz).ne'
  · exact withDensity_absolutelyContinuous _ _

theorem acceptanceFlow_inverse_le (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z)
    (h : μ.map e ≪ μ) : (acceptanceFlow μ e).map e.symm ≤ μ := by
  calc
    _ ≤ (μ.map e).map e.symm := Measure.map_mono (acceptanceFlow_le_map μ e h) e.symm.measurable
    _ = μ := by rw [Measure.map_map e.symm.measurable e.measurable]; simp

/-- Directed accepted edge flow. -/
noncomputable def acceptedEdges (ν : Measure Z) (e : Z ≃ᵐ Z) : Measure (Z × Z) :=
  ν.map (fun z => (z, e.symm z))

/-- Complete the accepted flow and its reverse by diagonal mass. The
marginals are μ+μ. This avoids any arbitrary kernel choices. -/
noncomputable def completedCoupling (μ ν : Measure Z) (e : Z ≃ᵐ Z) : Measure (Z × Z) :=
  acceptedEdges ν e + (acceptedEdges ν e).map Prod.swap +
    ((μ + μ) - (ν + ν.map e.symm)).map (fun z => (z, z))

theorem acceptedEdges_fst (ν : Measure Z) (e : Z ≃ᵐ Z) :
    (acceptedEdges ν e).map Prod.fst = ν := by
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) := measurable_id.prodMk e.symm.measurable
  rw [acceptedEdges, Measure.map_map measurable_fst hgraph]
  exact Measure.map_id

theorem acceptedEdges_snd (ν : Measure Z) (e : Z ≃ᵐ Z) :
    (acceptedEdges ν e).map Prod.snd = ν.map e.symm := by
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) := measurable_id.prodMk e.symm.measurable
  rw [acceptedEdges, Measure.map_map measurable_snd hgraph]
  rfl

theorem completedCoupling_marginals (μ ν : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : Z ≃ᵐ Z)
    (hν : ν ≤ μ) (hνinv : ν.map e.symm ≤ μ) :
    (completedCoupling μ ν e).map Prod.fst = μ + μ ∧
      (completedCoupling μ ν e).map Prod.snd = μ + μ := by
  let A := acceptedEdges ν e
  let R := (μ + μ) - (ν + ν.map e.symm)
  have hsum : ν + ν.map e.symm ≤ μ + μ := add_le_add hν hνinv
  have hR : R + (ν + ν.map e.symm) = μ + μ := Measure.sub_add_cancel_of_le hsum
  have hA1 : A.map Prod.fst = ν := acceptedEdges_fst ν e
  have hA2 : A.map Prod.snd = ν.map e.symm := acceptedEdges_snd ν e
  have hAS1 : (A.map Prod.swap).map Prod.fst = ν.map e.symm := by
    rw [Measure.map_map measurable_fst measurable_swap]
    exact hA2
  have hAS2 : (A.map Prod.swap).map Prod.snd = ν := by
    rw [Measure.map_map measurable_snd measurable_swap]
    exact hA1
  have hdiag : Measurable (fun z : Z => (z,z)) := measurable_id.prodMk measurable_id
  have hR1 : (R.map (fun z => (z,z))).map Prod.fst = R := by
    rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  have hR2 : (R.map (fun z => (z,z))).map Prod.snd = R := by
    rw [Measure.map_map measurable_snd hdiag]
    exact Measure.map_id
  constructor
  · change (A + A.map Prod.swap + R.map (fun z => (z,z))).map Prod.fst = μ + μ
    rw [Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst, hA1, hAS1, hR1]
    exact (add_comm _ _).trans hR
  · change (A + A.map Prod.swap + R.map (fun z => (z,z))).map Prod.snd = μ + μ
    rw [Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd, hA2, hAS2, hR2]
    calc
      ν.map e.symm + ν + R = R + (ν + ν.map e.symm) := by ac_rfl
      _ = μ + μ := hR

/-- The completed coupling detects exactly invariance along the
automorphism when its accepted flow has the full measure class. -/
theorem completedCoupling_ae_equal_iff
    (μ ν : Measure Z) (e : Z ≃ᵐ Z)
    (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (f : Z → ℝ) (hf : Measurable f) :
    (∀ᵐ z ∂completedCoupling μ ν e, f z.1 = f z.2) ↔
      ∀ᵐ z ∂μ, f z = f (e.symm z) := by
  let A := acceptedEdges ν e
  let R := (μ + μ) - (ν + ν.map e.symm)
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) :=
    measurable_id.prodMk e.symm.measurable
  have hdiag : Measurable (fun z : Z => (z,z)) := measurable_id.prodMk measurable_id
  have hpred : MeasurableSet {z : Z × Z | f z.1 = f z.2} :=
    measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd)
  constructor
  · intro h
    have hAle : A ≤ completedCoupling μ ν e := by
      exact (Measure.le_add_right (le_refl A)).trans (Measure.le_add_right le_rfl)
    have hA := hAle.absolutelyContinuous.ae_le h
    exact hμν.ae_le (ae_of_ae_map hgraph.aemeasurable hA)
  · intro h
    have hA : ∀ᵐ z ∂A, f z.1 = f z.2 :=
      (ae_map_iff hgraph.aemeasurable hpred).mpr (hνμ.ae_le h)
    have hAS : ∀ᵐ z ∂A.map Prod.swap, f z.1 = f z.2 :=
      (ae_map_iff measurable_swap.aemeasurable hpred).mpr (hA.mono (fun _ hz => hz.symm))
    have hR : ∀ᵐ z ∂R.map (fun z => (z,z)), f z.1 = f z.2 :=
      (ae_map_iff hdiag.aemeasurable hpred).mpr (Eventually.of_forall (fun _ => rfl))
    exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨hA, hAS⟩, hR⟩

/-- The concrete Metropolis L2 operator. The harmless common scaling
μ+μ keeps the diagonal-completion formula free of division of measures. -/
noncomputable def metropolisTransition (μ : Measure Z) [IsFiniteMeasure μ]
    (e : Z ≃ᵐ Z) (hmap : μ.map e ≪ μ) :
    Lp ℝ 2 (μ + μ) →L[ℝ] Lp ℝ 2 (μ + μ) :=
  couplingTransition (μ + μ) (completedCoupling μ (acceptanceFlow μ e) e)
    (completedCoupling_marginals μ (acceptanceFlow μ e) e
      (acceptanceFlow_le μ e) (acceptanceFlow_inverse_le μ e hmap)).1
    (completedCoupling_marginals μ (acceptanceFlow μ e) e
      (acceptanceFlow_le μ e) (acceptanceFlow_inverse_le μ e hmap)).2

theorem metropolisTransition_norm_le_one (μ : Measure Z) [IsFiniteMeasure μ]
    (e : Z ≃ᵐ Z) (hmap : μ.map e ≪ μ) : ‖metropolisTransition μ e hmap‖ ≤ 1 :=
  couplingTransition_norm_le_one _ _ _ _

theorem metropolisTransition_fixed_iff (μ : Measure Z) [IsFiniteMeasure μ]
    (e : Z ≃ᵐ Z) (hmap : μ.map e ≪ μ) (hback : μ ≪ μ.map e)
    (f : Lp ℝ 2 (μ + μ)) :
    metropolisTransition μ e hmap f = f ↔ ∀ᵐ z ∂μ, f z = f (e.symm z) := by
  unfold metropolisTransition
  rw [couplingTransition_fixed_iff]
  exact completedCoupling_ae_equal_iff μ (acceptanceFlow μ e) e
    (acceptanceFlow_equivalent μ e hback).2 (acceptanceFlow_equivalent μ e hback).1
    f (Lp.stronglyMeasurable f).measurable

end MeasureEquivalenceMarkov

#print axioms MeasureEquivalenceMarkov.acceptanceFlow_equivalent
#print axioms MeasureEquivalenceMarkov.completedCoupling_marginals
#print axioms MeasureEquivalenceMarkov.metropolisTransition_norm_le_one
#print axioms MeasureEquivalenceMarkov.metropolisTransition_fixed_iff
