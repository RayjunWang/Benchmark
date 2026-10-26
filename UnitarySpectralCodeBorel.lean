import UnitaryMeasurableSpectralSupports
import UnitarySpectralCodeNonzero
import Mathlib.Probability.Kernel.Composition.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace OperatorCoding

open MeasureUnitary SpectralDomination

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance : MeasurableSpace H := borel _
local instance : BorelSpace H := ⟨rfl⟩
local instance : MeasurableSpace (StrongUnitary H) := borel _
local instance : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem greedyMultiplicity_joint_measurable :
    Measurable (fun p : StrongUnitary H × SpectralCircle => fiberMultiplicity (greedySpectralSupport p.1) p.2) := by
  classical
  apply Measurable.ennreal_tsum
  intro n
  exact Measurable.ite (greedySpectralSupport_joint_measurableSet n) measurable_const measurable_const

def greedyLayerRegion : Set (StrongUnitary H × (SpectralCircle × ℕ)) :=
  {p | p.2.1 ∈ multiplicityLayer (greedySpectralSupport p.1) p.2.2}

theorem greedyLayerRegion_measurableSet : MeasurableSet (greedyLayerRegion (H := H)) := by
  change MeasurableSet {p : StrongUnitary H × (SpectralCircle × ℕ) |
    (p.2.2 : ℝ≥0∞) < fiberMultiplicity (greedySpectralSupport p.1) p.2.1}
  apply measurableSet_lt
  · exact (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      (measurable_snd.comp measurable_snd)
  · exact greedyMultiplicity_joint_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

def greedyCodeKernel (w : Measure ℕ) [IsFiniteMeasure w] :
    Kernel (StrongUnitary H) (SpectralCircle × ℕ) := by
  classical
  exact (greedyDominatingKernel.prod (Kernel.const _ w)).withDensity
    (fun U p => (greedyLayerRegion (H := H)).indicator (fun _ => 1) (U,p))

theorem greedyCodeKernel_apply (w : Measure ℕ) [IsFiniteMeasure w] (U : StrongUnitary H) :
    greedyCodeKernel w U = multiplicityLayerCode (greedyDominatingKernel U) (greedySpectralSupport U) w := by
  classical
  have hd : Measurable (Function.uncurry (fun (U : StrongUnitary H) (p : SpectralCircle × ℕ) =>
      (greedyLayerRegion (H := H)).indicator (fun _ => (1 : ℝ≥0∞)) (U,p))) :=
    measurable_const.indicator (greedyLayerRegion_measurableSet (H := H))
  rw [greedyCodeKernel, Kernel.withDensity_apply _ hd]
  rw [Kernel.prod_apply, Kernel.const_apply]
  change ((greedyDominatingKernel U).prod w).withDensity
    ((measureFiberSet (multiplicityLayer (greedySpectralSupport U))).indicator (fun _ => 1)) = _
  exact withDensity_indicator_one
    (measureFiberSet_measurable _ (multiplicityLayer_measurable _ (greedySpectralSupport_measurableSet U)))

instance greedyCodeKernel_finite (w : Measure ℕ) [IsFiniteMeasure w] :
    IsFiniteKernel (greedyCodeKernel (H := H) w) := by
  classical
  unfold greedyCodeKernel
  apply Kernel.isFiniteKernel_withDensity_of_bounded _ (B := 1) (by simp)
  intro U p
  simp only [Set.indicator_apply]
  split_ifs <;> simp

theorem greedyCodeKernel_ne_zero (w : Measure ℕ) [IsFiniteMeasure w]
    (hw : ∀ n, w {n} ≠ 0) (U : StrongUnitary H) : greedyCodeKernel w U ≠ 0 := by
  rw [greedyCodeKernel_apply]
  exact unitary_multiplicityLayerCode_ne_zero U (greedyDominatingKernel U)
    (greedySpectralSupport U) (greedySpectralSupport_measurableSet U)
    (fun n => (greedySpectralSupport_equivalent U n).1) w hw

theorem greedyCodeKernel_classification (w : Measure ℕ) [IsFiniteMeasure w]
    (hw : ∀ n, w {n} ≠ 0) (U V : StrongUnitary H) :
    (∃ W : H ≃ₗᵢ[ℂ] H, ∀ x, W (U x) = V (W x)) ↔
      (greedyCodeKernel w U ≪ greedyCodeKernel w V ∧ greedyCodeKernel w V ≪ greedyCodeKernel w U) := by
  rw [greedyCodeKernel_apply, greedyCodeKernel_apply]
  exact unitary_multiplicityLayerCode_classification U V _ _ _ _
    (greedySpectralSupport_measurableSet U) (greedySpectralSupport_measurableSet V)
    (fun n => (greedySpectralSupport_equivalent U n).1)
    (fun n => (greedySpectralSupport_equivalent U n).2)
    (fun n => (greedySpectralSupport_equivalent V n).1)
    (fun n => (greedySpectralSupport_equivalent V n).2) w hw

end OperatorCoding

#print axioms OperatorCoding.greedyCodeKernel_classification
