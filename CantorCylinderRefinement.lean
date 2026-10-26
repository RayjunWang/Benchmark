import CantorPrefixPerturbation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BenchmarkJump

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open MeasureUnitary

theorem cantorCylinder_constant_on_prefix (k : CantorCylinderIndex) (n : ℕ)
    (hk : ∀ i ∈ k.1, i < n) (s : Fin n → Bool) (x : HaarCantor) (hx : x ∈ prefixCylinder s) :
    x ∈ cantorCylinder k ↔ prefixPoint s ∈ cantorCylinder k := by
  have he : (fun i : k.1 => x i) = (fun i : k.1 => prefixPoint s i) := by
    funext i
    exact (hx ⟨i,hk i i.property⟩).trans ((prefixPoint_mem s) ⟨i,hk i i.property⟩).symm
  change ((fun i : k.1 => x i) ∈ k.2) ↔ ((fun i : k.1 => prefixPoint s i) ∈ k.2)
  rw [he]

theorem cantorCylinder_inter_prefix (k : CantorCylinderIndex) (n : ℕ)
    (hk : ∀ i ∈ k.1, i < n) (s : Fin n → Bool) :
    cantorCylinder k ∩ prefixCylinder s =
      if prefixPoint s ∈ cantorCylinder k then prefixCylinder s else ∅ := by
  classical
  ext x
  by_cases hp : prefixPoint s ∈ cantorCylinder k
  · simp only [if_pos hp, mem_inter_iff]
    exact ⟨fun h => h.2,fun hx => ⟨(cantorCylinder_constant_on_prefix k n hk s x hx).mpr hp,hx⟩⟩
  · simp only [if_neg hp, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxD hxC
    exact hp ((cantorCylinder_constant_on_prefix k n hk s x hxC).mp hxD)

theorem measure_eq_sum_prefix_inter (μ : Measure HaarCantor) (A : Set HaarCantor)
    (hA : MeasurableSet A) (n : ℕ) :
    μ A = ∑ s : Fin n → Bool, μ (A ∩ prefixCylinder s) := by
  have he : (⋃ s : Fin n → Bool, A ∩ prefixCylinder s) = A := by
    rw [← inter_iUnion, prefixCylinder_iUnion, inter_univ]
  have hd : Pairwise (fun (s t : Fin n → Bool) =>
      Disjoint (A ∩ prefixCylinder s) (A ∩ prefixCylinder t)) := by
    intro s t hst
    exact (prefixCylinder_pairwise_disjoint n hst).mono inter_subset_right inter_subset_right
  calc
    μ A = μ (⋃ s : Fin n → Bool, A ∩ prefixCylinder s) := congrArg μ he.symm
    _ = _ := by
      rw [measure_iUnion hd (fun s => hA.inter (isClopen_prefixCylinder s).isClosed.measurableSet),tsum_fintype]

theorem cantorCylinder_mass_prefix_sum (μ : Measure HaarCantor) (k : CantorCylinderIndex) (n : ℕ)
    (hk : ∀ i ∈ k.1, i < n) :
    μ (cantorCylinder k) = ∑ s : Fin n → Bool,
      if prefixPoint s ∈ cantorCylinder k then μ (prefixCylinder s) else 0 := by
  classical
  rw [measure_eq_sum_prefix_inter μ _ (cantorCylinder_measurable k) n]
  apply Finset.sum_congr rfl
  intro s _
  rw [cantorCylinder_inter_prefix k n hk s]
  split_ifs <;> simp

theorem cantorCylinder_real_prefix_sum (μ : Measure HaarCantor) [IsFiniteMeasure μ]
    (k : CantorCylinderIndex) (n : ℕ) (hk : ∀ i ∈ k.1, i < n) :
    μ.real (cantorCylinder k) = ∑ s : Fin n → Bool,
      if prefixPoint s ∈ cantorCylinder k then μ.real (prefixCylinder s) else 0 := by
  classical
  have h := congrArg ENNReal.toReal (cantorCylinder_mass_prefix_sum μ k n hk)
  rw [ENNReal.toReal_sum (fun s _ => by split_ifs <;> finiteness)] at h
  simpa only [measureReal_def,apply_ite ENNReal.toReal,ENNReal.toReal_zero] using h

end BenchmarkJump

#print axioms BenchmarkJump.cantorCylinder_real_prefix_sum
