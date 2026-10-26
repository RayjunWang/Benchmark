import UnitaryDominatedSpectralModel
import FiberMultiplicityBaseChange

/-! The complete measure-class invariant of an arbitrary unitary from its
actual countable cyclic decomposition, for any finite dominating support
presentation. The comparison uses the genuine common base μ+ν and its
Radon–Nikodym supports. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

 theorem unitary_multiplicityLayerCode_classification
    (U V : StrongUnitary H) (μ ν : Measure SpectralCircle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : ℕ → Set SpectralCircle)
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hUμ : ∀ n, greedySpectralMeasure U n ≪ μ.restrict (A n))
    (hμU : ∀ n, μ.restrict (A n) ≪ greedySpectralMeasure U n)
    (hVν : ∀ n, greedySpectralMeasure V n ≪ ν.restrict (B n))
    (hνV : ∀ n, ν.restrict (B n) ≪ greedySpectralMeasure V n)
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ n, w {n} ≠ 0) :
    (∃ W : H ≃ₗᵢ[ℂ] H, ∀ x, W (U x) = V (W x)) ↔
      (multiplicityLayerCode μ A w ≪ multiplicityLayerCode ν B w ∧
        multiplicityLayerCode ν B w ≪ multiplicityLayerCode μ A w) := by
  let ρ := μ + ν
  let C := rnSupport μ ρ
  let D := rnSupport ν ρ
  let A' := supportedFamily A C
  let B' := supportedFamily B D
  have hC : MeasurableSet C := rnSupport_measurable μ ρ
  have hD : MeasurableSet D := rnSupport_measurable ν ρ
  have hA' : ∀ n, MeasurableSet (A' n) := supportedFamily_measurable A hA C hC
  have hB' : ∀ n, MeasurableSet (B' n) := supportedFamily_measurable B hB D hD
  have hμρ : μ ≪ ρ.restrict C ∧ ρ.restrict C ≪ μ :=
    rnSupport_measureClass μ ρ (Measure.AbsolutelyContinuous.rfl.add_right ν)
  have hνρ : ν ≪ ρ.restrict D ∧ ρ.restrict D ≪ ν :=
    rnSupport_measureClass ν ρ (Measure.AbsolutelyContinuous.rfl.add_right' μ)
  have hAρ (n : ℕ) : μ.restrict (A n) ≪ ρ.restrict (A' n) ∧
      ρ.restrict (A' n) ≪ μ.restrict (A n) :=
    restrict_measureClass_baseChange μ ρ C (A n) (hA n) hμρ.1 hμρ.2
  have hBρ (n : ℕ) : ν.restrict (B n) ≪ ρ.restrict (B' n) ∧
      ρ.restrict (B' n) ≪ ν.restrict (B n) :=
    restrict_measureClass_baseChange ν ρ D (B n) (hB n) hνρ.1 hνρ.2
  have hUρ (n : ℕ) : greedySpectralMeasure U n ≪ ρ.restrict (A' n) :=
    (hUμ n).trans (hAρ n).1
  have hρU (n : ℕ) : ρ.restrict (A' n) ≪ greedySpectralMeasure U n :=
    (hAρ n).2.trans (hμU n)
  have hVρ (n : ℕ) : greedySpectralMeasure V n ≪ ρ.restrict (B' n) :=
    (hVν n).trans (hBρ n).1
  have hρV (n : ℕ) : ρ.restrict (B' n) ≪ greedySpectralMeasure V n :=
    (hBρ n).2.trans (hνV n)
  have hrep := unitaryDominatedFiber_classification U ρ A' hUρ hρU V B' hVρ hρV hA' hB'
  have hcode := multiplicityLayerCode_classification ρ A' B' hA' hB' w hw
  have hcodeA := multiplicityLayerCode_baseChange μ ρ A hA C hC hμρ.1 hμρ.2 w hw
  have hcodeB := multiplicityLayerCode_baseChange ν ρ B hB D hD hνρ.1 hνρ.2 w hw
  constructor
  · intro hW
    have hmid := hcode.mpr (hrep.mp hW)
    exact ⟨hcodeA.1.trans (hmid.1.trans hcodeB.2),
      hcodeB.1.trans (hmid.2.trans hcodeA.2)⟩
  · rintro ⟨hAB,hBA⟩
    apply hrep.mpr
    apply hcode.mp
    exact ⟨hcodeA.2.trans (hAB.trans hcodeB.1),
      hcodeB.2.trans (hBA.trans hcodeA.1)⟩

end
end OperatorCoding

#print axioms OperatorCoding.unitary_multiplicityLayerCode_classification
