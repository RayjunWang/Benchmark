import OperatorBorelNormalization
import HilbertSequenceTopology
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-! Adjoint evaluation is measurable for the strong Borel structure on
operators on the canonical separable Hilbert space. -/

namespace OperatorCoding

theorem canonical_adjoint_coordinate (T : CanonicalOperator) (x : CanonicalHilbert) (n : ℕ) :
    (T.adjoint x) n = inner ℂ (T (lp.single 2 n (1 : ℂ))) x := by
  simpa [lp.inner_single_left] using
    T.adjoint_inner_right (lp.single 2 n (1 : ℂ)) x

theorem canonical_adjoint_apply_measurable (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => T.adjoint x) := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopologyOn CanonicalHilbert
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : BorelSpace CanonicalOperator := ⟨rfl⟩
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  apply canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun T : CanonicalOperator => fun n : ℕ => (T.adjoint x) n)
  apply measurable_pi_iff.mpr
  intro n
  have he : Continuous (fun T : CanonicalOperator => T (lp.single 2 n (1 : ℂ))) :=
    (continuous_apply _).comp continuous_induced_dom
  have hi : Continuous (fun T : CanonicalOperator => inner ℂ (T (lp.single 2 n (1 : ℂ))) x) :=
    he.inner continuous_const
  simpa only [canonical_adjoint_coordinate] using hi.measurable

end OperatorCoding

#print axioms OperatorCoding.canonical_adjoint_apply_measurable
