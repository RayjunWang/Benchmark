import OperatorMeasurableEvaluation

/-! The strong topology on the unitary group is determined by countably
many dense vector evaluations. This identifies its Borel structure without
using operator-norm measurability in place of strong measurability. -/

open Filter Topology TopologicalSpace

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]

noncomputable abbrev strongUnitaryDenseTopology : TopologicalSpace (StrongUnitary H) :=
  TopologicalSpace.induced (fun u : StrongUnitary H => fun n : ℕ => u (denseSeq H n)) inferInstance

variable {H}

theorem strongUnitary_denseEvaluation_continuous (x : H) :
    @Continuous (StrongUnitary H) H (strongUnitaryDenseTopology H) inferInstance (fun u => u x) := by
  letI : TopologicalSpace (StrongUnitary H) := strongUnitaryDenseTopology H
  apply continuous_iff_continuousAt.mpr
  intro U
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (denseRange_denseSeq H).exists_dist_lt x (by positivity : (0 : ℝ) < ε / 3)
  have hmap : Continuous (fun V : StrongUnitary H => fun k : ℕ => V (denseSeq H k)) :=
    continuous_induced_dom
  have he : Continuous (fun V : StrongUnitary H => V (denseSeq H n)) :=
    (continuous_apply n).comp hmap
  have hv := Metric.continuousAt_iff'.mp (he.continuousAt (x := U)) (ε / 3) (by positivity)
  filter_upwards [hv] with V hV
  have h₁ := dist_triangle (V x) (V (denseSeq H n)) (U x)
  have h₂ := dist_triangle (V (denseSeq H n)) (U (denseSeq H n)) (U x)
  have hVnorm : dist (V x) (V (denseSeq H n)) = dist x (denseSeq H n) :=
    V.toIsometryEquiv.dist_eq _ _
  have hUnorm : dist (U (denseSeq H n)) (U x) = dist x (denseSeq H n) := by
    exact (U.toIsometryEquiv.dist_eq _ _).trans (dist_comm _ _)
  rw [hVnorm] at h₁
  rw [hUnorm] at h₂
  linarith

theorem strongUnitary_topology_eq_dense :
    instTopologicalSpaceStrongUnitary H = strongUnitaryDenseTopology H := by
  have hforward : @Continuous (StrongUnitary H) (StrongUnitary H)
      (instTopologicalSpaceStrongUnitary H) (strongUnitaryDenseTopology H) id := by
    apply continuous_induced_rng.mpr
    exact continuous_pi (fun n => strongUnitary_continuous_eval (denseSeq H n))
  have hbackward : @Continuous (StrongUnitary H) (StrongUnitary H)
      (strongUnitaryDenseTopology H) (instTopologicalSpaceStrongUnitary H) id := by
    exact (@strongUnitary_continuous_iff H _ _ (StrongUnitary H)
      (strongUnitaryDenseTopology H) id).mpr strongUnitary_denseEvaluation_continuous
  exact le_antisymm
    (by simpa only [induced_id] using continuous_iff_le_induced.mp hforward)
    (by simpa only [induced_id] using continuous_iff_le_induced.mp hbackward)

instance strongUnitary_secondCountable [SecondCountableTopology H] :
    SecondCountableTopology (StrongUnitary H) := by
  rw [strongUnitary_topology_eq_dense]
  exact secondCountableTopology_induced _ _ _

theorem strongUnitary_measurable_of_evaluations {X : Type*} [MeasurableSpace X]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : X → StrongUnitary H) (hf : ∀ x : H, Measurable (fun a => f a x)) :
    @Measurable X (StrongUnitary H) inferInstance (borel (StrongUnitary H)) f := by
  apply measurable_iff_comap_le.mpr
  change (borel (StrongUnitary H)).comap f ≤ (inferInstance : MeasurableSpace X)
  rw [strongUnitary_topology_eq_dense, borel_comap]
  rw [MeasurableSpace.comap_comp]
  have hb : (inferInstance : MeasurableSpace (ℕ → H)) = borel (ℕ → H) := BorelSpace.measurable_eq
  rw [← hb]
  exact measurable_iff_comap_le.mp (measurable_pi_iff.mpr (fun n => hf (denseSeq H n)))

theorem operatorUnitaryPair_measurable (i : Bool) :
    @Measurable CanonicalOperator (StrongUnitary CanonicalHilbert)
      (operatorStrongBorel CanonicalHilbert) (borel (StrongUnitary CanonicalHilbert))
      (fun T => operatorUnitaryPair T i) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  exact strongUnitary_measurable_of_evaluations _ (fun x => operatorUnitaryPair_apply_measurable i x)

end OperatorCoding

#print axioms OperatorCoding.operatorUnitaryPair_measurable
