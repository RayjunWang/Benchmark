import UnitarySpectralMeasureBorel
import KernelSpectralSupports

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

def spectralBasePoint : SpectralCircle := ⟨1, by simp⟩

def greedyWeightedKernel (n : ℕ) : Kernel (StrongUnitary H) SpectralCircle :=
  weightedKernel (fun U n => greedySpectralMeasure U n) greedySpectralMeasure_measurable n

def greedyDominatingKernel : Kernel (StrongUnitary H) SpectralCircle :=
  dominatingKernel (fun U n => greedySpectralMeasure U n) greedySpectralMeasure_measurable spectralBasePoint

instance greedyWeightedKernel_finite (n : ℕ) : IsFiniteKernel (greedyWeightedKernel (H := H) n) := by
  unfold greedyWeightedKernel
  infer_instance

instance greedyDominatingKernel_finite : IsFiniteKernel (greedyDominatingKernel (H := H)) := by
  unfold greedyDominatingKernel
  infer_instance

def greedySpectralSupport (U : StrongUnitary H) (n : ℕ) : Set SpectralCircle :=
  kernelSupport (greedyWeightedKernel n) greedyDominatingKernel U

theorem greedySpectralSupport_measurableSet (U : StrongUnitary H) (n : ℕ) :
    MeasurableSet (greedySpectralSupport U n) :=
  measurableSet_kernelSupport _ _ _

theorem greedySpectralSupport_joint_measurableSet (n : ℕ) :
    MeasurableSet {p : StrongUnitary H × SpectralCircle | p.2 ∈ greedySpectralSupport p.1 n} :=
  measurableSet_kernelSupport_joint _ _

theorem greedyWeightedKernel_ac_dominating (U : StrongUnitary H) (n : ℕ) :
    greedyWeightedKernel n U ≪ greedyDominatingKernel U := by
  change weight (fun n => greedySpectralMeasure U n) n • greedySpectralMeasure U n ≪ _
  exact (measure_ac_dominatingKernel (fun V n => greedySpectralMeasure V n)
    greedySpectralMeasure_measurable spectralBasePoint U n).smul_left _

theorem greedySpectralSupport_equivalent (U : StrongUnitary H) (n : ℕ) :
    greedySpectralMeasure U n ≪ (greedyDominatingKernel U).restrict (greedySpectralSupport U n) ∧
      (greedyDominatingKernel U).restrict (greedySpectralSupport U n) ≪ greedySpectralMeasure U n := by
  have h := kernel_support_equivalent (greedyWeightedKernel n) greedyDominatingKernel U
    (greedyWeightedKernel_ac_dominating U n)
  have hscale : greedySpectralMeasure U n ≪ greedyWeightedKernel n U :=
    Measure.absolutelyContinuous_smul (weight_ne_zero (greedySpectralMeasure U) n)
  exact ⟨hscale.trans h.1, h.2.trans Measure.smul_absolutelyContinuous⟩

end OperatorCoding

#print axioms OperatorCoding.greedySpectralSupport_equivalent
