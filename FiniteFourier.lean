import Mathlib.Tactic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Finite Hilbert-valued Fourier identities for the finite-torus feasibility check.
This file is a separate development and does not alter the earlier checks.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceFourier

variable {G E : Type*} [AddCommGroup G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma character_orthogonality_sum (χ ψ : AddChar G ℂ) :
    (∑ x, conj (χ x) * ψ x) =
      if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  simp only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
    Fintype.expect_eq_sum_div_card] at h
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  split_ifs with heq
  · simp only [heq, ite_true] at h
    have hh := (div_eq_iff hc).mp h
    simpa [heq, mul_comm] using hh
  · simp only [heq, ite_false] at h
    have hh := (div_eq_iff hc).mp h
    simpa [mul_comm] using hh

lemma synthesis_inner (v w : AddChar G ℂ → E) :
    (∑ x, inner ℂ (∑ χ : AddChar G ℂ, χ x • v χ)
      (∑ ψ : AddChar G ℂ, ψ x • w ψ)) =
      (Fintype.card G : ℂ) * ∑ χ : AddChar G ℂ, inner ℂ (v χ) (w χ) := by
  classical
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  calc
    (∑ x, ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
        conj (χ x) * (ψ x * inner ℂ (v χ) (w ψ))) =
        ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          (∑ x, conj (χ x) * ψ x) * inner ℂ (v χ) (w ψ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (Fintype.card G : ℂ) *
        ∑ χ : AddChar G ℂ, inner ℂ (v χ) (w χ) := by
      simp_rw [character_orthogonality_sum]
      simp [Finset.mul_sum]

theorem synthesis_parseval (v : AddChar G ℂ → E) :
    (∑ x, ‖∑ χ : AddChar G ℂ, χ x • v χ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ, ‖v χ‖ ^ 2 := by
  have h := synthesis_inner v v
  simp only [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

noncomputable def coefficient (F : G → E) (χ : AddChar G ℂ) : E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ y, conj (χ y) • F y

theorem inversion (F : G → E) (x : G) :
    (∑ χ : AddChar G ℂ, χ x • coefficient F χ) = F x := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hχ (χ : AddChar G ℂ) (y : G) :
      χ x * conj (χ y) = χ (x - y) := by
    rw [χ.map_sub_eq_div, div_eq_mul_inv, χ.inv_apply_eq_conj]
  calc
    (∑ χ : AddChar G ℂ, χ x • coefficient F χ) =
        (Fintype.card G : ℂ)⁻¹ • ∑ y,
          (∑ χ : AddChar G ℂ, χ (x - y)) • F y := by
      simp only [coefficient, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro χ _
      rw [← hχ]
      congr 1
      ring
    _ = (Fintype.card G : ℂ)⁻¹ • ((Fintype.card G : ℂ) • F x) := by
      simp [AddChar.sum_apply_eq_ite, sub_eq_zero]
    _ = F x := by simp [smul_smul, hc]

theorem translation_energy (F : G → E) (a : G) :
    (∑ x, ‖F (x + a) - F x‖ ^ 2) =
      (Fintype.card G : ℝ) *
        ∑ χ : AddChar G ℂ, ‖χ a - 1‖ ^ 2 * ‖coefficient F χ‖ ^ 2 := by
  have hpoint (x : G) : F (x + a) - F x =
      ∑ χ : AddChar G ℂ, χ x • ((χ a - 1) • coefficient F χ) := by
    rw [← inversion F (x + a), ← inversion F x, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro χ _
    rw [χ.map_add_eq_mul, mul_smul, sub_smul, one_smul, smul_sub]
  simp_rw [hpoint]
  rw [synthesis_parseval]
  simp [norm_smul, mul_pow]

lemma translation_family_energy {K : Type*} [Fintype K] (c : K → G) (F : G → E) :
      (∑ i, ∑ x, ‖F (x + c i) - F x‖ ^ 2) =
        (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
          (∑ i, ‖χ (c i) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 := by
  simp_rw [translation_energy]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- A comparison of scalar Fourier multipliers gives the same comparison
for every function with values in a complex inner product space. -/
theorem spectral_comparison {I J : Type*} [Fintype I] [Fintype J]
    (a : I → G) (b : J → G) (C : ℝ)
    (hmult : ∀ χ : AddChar G ℂ,
      (∑ i, ‖χ (a i) - 1‖ ^ 2) ≤ C * ∑ j, ‖χ (b j) - 1‖ ^ 2)
    (F : G → E) :
    (∑ i, ∑ x, ‖F (x + a i) - F x‖ ^ 2) ≤
      C * ∑ j, ∑ x, ‖F (x + b j) - F x‖ ^ 2 := by
  rw [translation_family_energy a F, translation_family_energy b F]
  calc
    (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
        (∑ i, ‖χ (a i) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 ≤
        (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
          (C * ∑ j, ‖χ (b j) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun χ _ =>
        mul_le_mul_of_nonneg_right (hmult χ) (sq_nonneg _)
    _ = C * ((Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
        (∑ j, ‖χ (b j) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2) := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      ring

end MeasureEquivalenceFourier

#print axioms MeasureEquivalenceFourier.synthesis_parseval
#print axioms MeasureEquivalenceFourier.inversion
#print axioms MeasureEquivalenceFourier.translation_energy
#print axioms MeasureEquivalenceFourier.spectral_comparison
