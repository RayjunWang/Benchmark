import RestrictedDensity
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem exponentialMeasure_ac_volume : exponentialMeasure ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

theorem volume_ac_exponentialMeasure : (volume : Measure ℝ) ≪ exponentialMeasure :=
  withDensity_absolutelyContinuous' measurable_exponentialDensity.aemeasurable
    (ae_of_all _ (fun t => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'))

theorem finite_exponential_ac_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => exponentialMeasure) ≪ (volume : Measure (Fin n → ℝ)) := by
  induction n with
  | zero =>
    have he : (fun _ : Fin 0 => exponentialMeasure) = (fun _ : Fin 0 => (volume : Measure ℝ)) :=
      funext (fun i => Fin.elim0 i)
    rw [he]
    exact Measure.AbsolutelyContinuous.rfl
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hm : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => exponentialMeasure))
        (exponentialMeasure.prod (Measure.pi (fun _ : Fin n => exponentialMeasure))) :=
      measurePreserving_piFinSuccAbove (fun _ => exponentialMeasure) 0
    have hv : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hb := e.symm.measurableEmbedding.absolutelyContinuous_map
      (exponentialMeasure_ac_volume.prod ih)
    rw [(hm.symm e).map_eq, (hv.symm e).map_eq] at hb
    exact hb

theorem finite_volume_ac_exponential (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) ≪ Measure.pi (fun _ : Fin n => exponentialMeasure) := by
  induction n with
  | zero =>
    have he : (fun _ : Fin 0 => exponentialMeasure) = (fun _ : Fin 0 => (volume : Measure ℝ)) :=
      funext (fun i => Fin.elim0 i)
    rw [he]
    exact Measure.AbsolutelyContinuous.rfl
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hm : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => exponentialMeasure))
        (exponentialMeasure.prod (Measure.pi (fun _ : Fin n => exponentialMeasure))) :=
      measurePreserving_piFinSuccAbove (fun _ => exponentialMeasure) 0
    have hv : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hb := e.symm.measurableEmbedding.absolutelyContinuous_map
      (volume_ac_exponentialMeasure.prod ih)
    rw [(hv.symm e).map_eq, (hm.symm e).map_eq] at hb
    exact hb

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.finite_volume_ac_exponential
