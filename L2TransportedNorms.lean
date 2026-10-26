import L2TransportedMatrix
import L2FiniteOnes

/-! The two constant-vector norms of one genuine twisted matrix
coefficient agree. The proof uses finite-support compression and the
commutative multiplication algebra, instead of postulating a trace. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureEquivalenceL2Transport

open MeasureEquivalenceL2Restriction MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem pullback_symm_eq (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) :
    (pullbackEquiv μ e he).symm = pullbackEquiv μ e.symm he.symm := by
  apply LinearIsometryEquiv.ext
  intro f
  apply (pullbackEquiv μ e he).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (pullback_inverse μ μ e e.symm he he.symm
    (Eventually.of_forall (fun x => e.symm_apply_apply x)) f).symm

theorem transported_adjoint (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    (transportedOperator μ d e hd he A B hB T).adjoint =
      transportedOperator μ e d he hd B A hA T.adjoint := by
  simp only [transportedOperator, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, pullback_symm_eq,
    globalize_adjoint μ A B hA hB, MeasurableEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

theorem restrict_pullback_finiteOne
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (A C : Set X) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hfinA : μ A ≠ ∞) (hfinC : μ C ≠ ∞) (hsub : e '' A ⊆ C) :
    restrictMap μ A (pullbackEquiv μ e he (finiteOne μ C hC hfinC)) =
      restrictedOne μ A hfinA := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (pullbackEquiv μ e he (finiteOne μ C hC hfinC)),
    ae_restrict_of_ae (pullback_coe μ e he (finiteOne μ C hC hfinC)),
    ae_restrict_of_ae (he.quasiMeasurePreserving.ae (finiteOne_coe μ C hC hfinC)),
    restrictedOne_coe μ A hfinA, ae_restrict_mem hA] with x hr hp hc hone hx
  rw [hr, hp, hc, hone]
  exact Set.indicator_of_mem (hsub (mem_image_of_mem e hx)) _

theorem transported_finiteOne_norm
    (d e : X ≃ᵐ X) (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B C : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfinA : μ A ≠ ∞) (hfinC : μ C ≠ ∞) (hsub : e '' A ⊆ C)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    ‖transportedOperator μ d e hd he A B hB T (finiteOne μ C hC hfinC)‖ =
      ‖T (restrictedOne μ A hfinA)‖ := by
  change ‖pullbackEquiv μ d.symm hd.symm
    (zeroExtend μ B hB (T (restrictMap μ A
      (pullbackEquiv μ e he (finiteOne μ C hC hfinC)))))‖ = _
  rw [LinearIsometryEquiv.norm_map, zeroExtend_norm,
    restrict_pullback_finiteOne μ e he A C hA hC hfinA hfinC hsub]

theorem twisted_coefficient_constant_norm_eq_adjoint
    (d e : X ≃ᵐ X) (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f)) :
    ‖T (restrictedOne μ A hfinA)‖ = ‖T.adjoint (restrictedOne μ B hfinB)‖ := by
  let C := e '' A ∪ d '' B
  have hEA : MeasurableSet (e '' A) := e.measurableEmbedding.measurableSet_image.mpr hA
  have hDB : MeasurableSet (d '' B) := d.measurableEmbedding.measurableSet_image.mpr hB
  have hC : MeasurableSet C := hEA.union hDB
  have hfC : μ C ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (measure_union_le _ _)
    rw [measure_image μ e he A hA, measure_image μ d hd B hB]
    exact ENNReal.add_ne_top.mpr ⟨hfinA,hfinB⟩
  let S := transportedOperator μ d e hd he A B hB T
  have hin (f : Lp ℂ 2 μ) : S (indicatorL2 μ hC f) = S f := by
    calc
      S (indicatorL2 μ hC f) = S (indicatorL2 μ hEA (indicatorL2 μ hC f)) :=
        (transported_input_supported μ d e hd he A B hA hB T _).symm
      _ = S (indicatorL2 μ hEA f) := by
        rw [indicatorL2_nested μ (e '' A) C hEA hC subset_union_left]
      _ = S f := transported_input_supported μ d e hd he A B hA hB T f
  have hout (f : Lp ℂ 2 μ) : indicatorL2 μ hC (S f) = S f := by
    calc
      indicatorL2 μ hC (S f) = indicatorL2 μ hC (indicatorL2 μ hDB (S f)) := by
        rw [transported_output_supported μ d e hd he A B hB T f]
      _ = indicatorL2 μ hDB (S f) :=
        indicatorL2_nested_reverse μ (d '' B) C hDB hC subset_union_right (S f)
      _ = S f := transported_output_supported μ d e hd he A B hB T f
  have hnorm := finite_supported_norm_adjoint μ C hC hfC S
    (transported_commutes_indicator μ d e hd he A B hB T hT) hin hout
    (restrictedOne μ C hfC)
  rw [zeroExtend_restrictedOne] at hnorm
  change ‖transportedOperator μ d e hd he A B hB T (finiteOne μ C hC hfC)‖ =
    ‖(transportedOperator μ d e hd he A B hB T).adjoint (finiteOne μ C hC hfC)‖ at hnorm
  rw [transported_adjoint μ d e hd he A B hA hB T,
    transported_finiteOne_norm μ d e hd he A B C hA hB hC hfinA hfC subset_union_left,
    transported_finiteOne_norm μ e d he hd B A C hB hA hC hfinB hfC subset_union_right] at hnorm
  exact hnorm

end
end MeasureEquivalenceL2Transport

#print axioms MeasureEquivalenceL2Transport.twisted_coefficient_constant_norm_eq_adjoint
