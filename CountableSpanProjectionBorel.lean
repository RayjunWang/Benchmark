import FiniteOrthogonalProjection
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Projection onto the closed span of a Borel countable family is
Borel. Finite Gram--Schmidt coefficient sums supply the actual limits. -/

open MeasureTheory Set Finset Filter Topology InnerProductSpace
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closedFamilySpan (f : ℕ → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range f)).topologicalClosure

instance closedFamilySpan_complete (f : ℕ → H) : CompleteSpace (closedFamilySpan f) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

theorem starProjection_eq_of_submodule_eq (P Q : Submodule ℂ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (hPQ : P = Q) :
    P.starProjection = Q.starProjection := by
  subst Q
  rfl

theorem finiteFamilySpan_mono (f : ℕ → H) : Monotone (finiteFamilySpan f) := by
  intro n m hnm
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hnm, rfl⟩

theorem iSup_finiteFamilySpan (f : ℕ → H) :
    (⨆ n : ℕ, finiteFamilySpan f n) = Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply (le_iSup (finiteFamilySpan f) (i+1))
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self i, rfl⟩

theorem finiteOrthogonalProjection_tendsto (f : ℕ → H)
    (horth : Pairwise (fun i j => inner ℂ (f i) (f j) = 0)) (x : H) :
    Tendsto (fun n => finiteOrthogonalProjection f n x) atTop
      (𝓝 ((closedFamilySpan f).starProjection x)) := by
  letI : ((⨆ n, finiteFamilySpan f n).topologicalClosure).HasOrthogonalProjection := by
    rw [iSup_finiteFamilySpan]
    change (closedFamilySpan f).HasOrthogonalProjection
    infer_instance
  have h := Submodule.starProjection_tendsto_closure_iSup (finiteFamilySpan f)
    (finiteFamilySpan_mono f) x
  have heq := starProjection_eq_of_submodule_eq
    (⨆ n, finiteFamilySpan f n).topologicalClosure (closedFamilySpan f)
      (congrArg Submodule.topologicalClosure (iSup_finiteFamilySpan f))
  simpa only [heq, finiteOrthogonalProjection_eq_starProjection f horth] using h

variable {S : Type*} [MeasurableSpace S] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]

theorem closedFamilySpan_projection_measurable (f : S → ℕ → H)
    (hf : ∀ i, Measurable (fun s => f s i)) (x : S → H) (hx : Measurable x) :
    Measurable (fun s => (closedFamilySpan (f s)).starProjection (x s)) := by
  let g : S → ℕ → H := fun s => gramSchmidt ℂ (f s)
  have hg : ∀ i, Measurable (fun s => g s i) := measurable_gramSchmidt f hf
  have hspan (s : S) : closedFamilySpan (g s) = closedFamilySpan (f s) := by
    unfold closedFamilySpan g
    rw [span_gramSchmidt]
  have hlim : Tendsto (fun n s => finiteOrthogonalProjection (g s) n (x s)) atTop
      (𝓝 (fun s => (closedFamilySpan (f s)).starProjection (x s))) := by
    apply tendsto_pi_nhds.mpr
    intro s
    have heq := starProjection_eq_of_submodule_eq (closedFamilySpan (g s))
      (closedFamilySpan (f s)) (hspan s)
    simpa only [heq] using
      finiteOrthogonalProjection_tendsto (g s) (gramSchmidt_pairwise_orthogonal ℂ (f s)) (x s)
  exact measurable_of_tendsto_metrizable (fun n => finiteOrthogonalProjection_measurable g hg x hx n) hlim

end
end MeasureUnitary

#print axioms MeasureUnitary.closedFamilySpan_projection_measurable
