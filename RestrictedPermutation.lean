import RestrictedModulus
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def blockSwapFun (N k : ℕ) : ℕ :=
  if k < N then N + k else if k < 2 * N then k - N else k

theorem blockSwap_involutive (N : ℕ) : Function.Involutive (blockSwapFun N) := by
  intro k
  unfold blockSwapFun
  split_ifs <;> omega

def blockSwap (N : ℕ) : Equiv.Perm ℕ where
  toFun := blockSwapFun N
  invFun := blockSwapFun N
  left_inv := blockSwap_involutive N
  right_inv := blockSwap_involutive N

theorem blockSwap_small (N k : ℕ) (hk : k < N) : blockSwap N k = N + k := by
  exact if_pos hk

theorem blockSwap_large (N k : ℕ) (hk : 2 * N ≤ k) : blockSwap N k = k := by
  change blockSwapFun N k = k
  unfold blockSwapFun
  rw [if_neg (by omega), if_neg (not_lt.mpr hk)]

theorem blockSwap_finite_support (N : ℕ) : {k | blockSwap N k ≠ k}.Finite := by
  apply (Finset.range (2 * N)).finite_toSet.subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  exact hk (blockSwap_large N k (le_of_not_gt h))

def permute (e : Equiv.Perm ℕ) (x : RealSequences) : RealSequences := fun k => x (e k)

theorem measurable_permute (e : Equiv.Perm ℕ) : Measurable (permute e) :=
  measurable_pi_lambda _ (fun k => measurable_pi_apply (e k))

theorem measurePreserving_permute (e : Equiv.Perm ℕ) :
    MeasurePreserving (permute e) tailProbability tailProbability := by
  constructor
  · exact measurable_permute e
  · exact Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => baseMeasure) e.injective

theorem disjoint_image_blockSwap (s : Finset ℕ) (N : ℕ) (hs : s ⊆ Finset.range N) :
    Disjoint s (s.image (blockSwap N)) := by
  apply Finset.disjoint_left.mpr
  intro k hk hki
  obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hki
  have hkN := Finset.mem_range.mp (hs hk)
  have hjN := Finset.mem_range.mp (hs hj)
  rw [blockSwap_small N j hjN] at hjk
  omega

theorem cylinder_blockSwap_independent (s : Finset ℕ) (N : ℕ) (hs : s ⊆ Finset.range N)
    (A : Set (s → ℝ)) (hA : MeasurableSet A) :
    tailProbability.real (cylinder s A ∩ (permute (blockSwap N)) ⁻¹' cylinder s A) =
      (tailProbability.real (cylinder s A)) ^ 2 := by
  let e := blockSwap N
  let T : Finset ℕ := s.image e
  let relabel : (T → ℝ) → (s → ℝ) := fun z i =>
    z ⟨e i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hr : Measurable relabel := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hf : ProbabilityTheory.iIndepFun (fun i (x : RealSequences) => x i) tailProbability :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => baseMeasure)
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hd : Disjoint s T := disjoint_image_blockSwap s N hs
  have hi := ProbabilityTheory.iIndepFun.indepFun_finset s T hd hf
    (fun i => measurable_pi_apply i)
  have hi' : ProbabilityTheory.IndepFun (fun (x : RealSequences) (i : s) => x i)
      (fun (x : RealSequences) (i : s) => x (e i)) tailProbability := by
    simpa only [Function.comp_apply, id_eq, relabel] using hi.comp measurable_id hr
  have he := hi'.measure_inter_preimage_eq_mul A A hA hA
  have hBm : MeasurableSet (cylinder s A : Set RealSequences) := hA.cylinder s
  have hm : tailProbability ((permute e) ⁻¹' cylinder s A) = tailProbability (cylinder s A) := by
    rw [← Measure.map_apply (measurable_permute e) hBm, (measurePreserving_permute e).map_eq]
  change tailProbability (cylinder s A ∩ (permute e) ⁻¹' cylinder s A) =
    tailProbability (cylinder s A) * tailProbability ((permute e) ⁻¹' cylinder s A) at he
  rw [hm] at he
  change (tailProbability (cylinder s A ∩ (permute e) ⁻¹' cylinder s A)).toReal =
    (tailProbability (cylinder s A)).toReal ^ 2
  rw [he, ENNReal.toReal_mul, pow_two]

end MeasureEquivalenceRestrictedProduct

#print axioms MeasureEquivalenceRestrictedProduct.measurePreserving_permute
#print axioms MeasureEquivalenceRestrictedProduct.cylinder_blockSwap_independent
