import OperatorFreeRepresentation
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Logic.Equiv.Nat

/-! A fixed, explicit Hilbert-space identification for the tuple coding:
ℓ²(ℕ, ℓ²(ℕ, ℂ)) ≃ ℓ²(ℕ × ℕ, ℂ) ≃ ℓ²(ℕ, ℂ). -/

open scoped ENNReal

namespace OperatorCoding

noncomputable section

abbrev MatrixHilbert := lp (fun _ : ℕ × ℕ => ℂ) 2

def flattenHilbertSum (x : HilbertSum CanonicalHilbert) : MatrixHilbert :=
  ⟨fun p => x p.1 p.2, by
    apply memℓp_gen
    apply (summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).mpr
    constructor
    · intro i
      exact (x i).property.summable (by norm_num)
    · have hrow : ∀ i, (∑' j, ‖x i j‖ ^ (2 : ℝ≥0∞).toReal) = ‖x i‖ ^ (2 : ℝ≥0∞).toReal :=
        fun i => (lp.norm_rpow_eq_tsum (by norm_num) (x i)).symm
      simp_rw [hrow]
      exact x.property.summable (by norm_num)⟩

def matrixHilbertRow (y : MatrixHilbert) (i : ℕ) : CanonicalHilbert :=
  ⟨fun j => y (i, j), by
    apply memℓp_gen
    exact ((summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).mp
      (y.property.summable (by norm_num))).1 i⟩

def foldMatrixHilbert (y : MatrixHilbert) : HilbertSum CanonicalHilbert :=
  ⟨fun i => matrixHilbertRow y i, by
    apply memℓp_gen
    have hrows := ((summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).mp
      (y.property.summable (by norm_num))).2
    have heq : (fun i => ‖matrixHilbertRow y i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ∑' j, ‖y (i, j)‖ ^ (2 : ℝ≥0∞).toReal) := by
      funext i
      exact lp.norm_rpow_eq_tsum (by norm_num) (matrixHilbertRow y i)
    rw [heq]
    exact hrows⟩

theorem flattenHilbertSum_norm (x : HilbertSum CanonicalHilbert) : ‖flattenHilbertSum x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  change (∑' p : ℕ × ℕ, ‖x p.1 p.2‖ ^ (2 : ℝ≥0∞).toReal) =
    ∑' i, ‖x i‖ ^ (2 : ℝ≥0∞).toReal
  have hfubini := ((flattenHilbertSum x).property.summable (by norm_num)).tsum_prod'
    (fun i => (x i).property.summable (by norm_num))
  change (∑' p : ℕ × ℕ, ‖x p.1 p.2‖ ^ (2 : ℝ≥0∞).toReal) =
    ∑' i, ∑' j, ‖x i j‖ ^ (2 : ℝ≥0∞).toReal at hfubini
  rw [hfubini]
  apply tsum_congr
  intro i
  exact (lp.norm_rpow_eq_tsum (by norm_num) (x i)).symm

def hilbertSumMatrixEquiv : HilbertSum CanonicalHilbert ≃ₗᵢ[ℂ] MatrixHilbert where
  toLinearEquiv :=
    { toFun := flattenHilbertSum
      invFun := foldMatrixHilbert
      left_inv := by
        intro x
        apply lp.ext
        funext i
        apply lp.ext
        funext j
        rfl
      right_inv := by
        intro y
        apply lp.ext
        funext p
        rfl
      map_add' := by
        intro x y
        apply lp.ext
        funext p
        rfl
      map_smul' := by
        intro c x
        apply lp.ext
        funext p
        rfl }
  norm_map' := flattenHilbertSum_norm

def reindexHilbert {I J : Type*} (e : I ≃ J) :
    lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => ℂ) 2 where
  toLinearEquiv :=
    { toFun := fun x => ⟨fun j => x (e.symm j), by
        apply memℓp_gen
        exact e.symm.summable_iff.mpr (x.property.summable (by norm_num))⟩
      invFun := fun y => ⟨fun i => y (e i), by
        apply memℓp_gen
        exact e.summable_iff.mpr (y.property.summable (by norm_num))⟩
      left_inv := by intro x; apply lp.ext; funext i; exact congrArg x (e.symm_apply_apply i)
      right_inv := by intro y; apply lp.ext; funext j; exact congrArg y (e.apply_symm_apply j)
      map_add' := by intro x y; apply lp.ext; funext j; rfl
      map_smul' := by intro c x; apply lp.ext; funext j; rfl }
  norm_map' := by
    intro x
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ℝ≥0∞).toReal)

/-- The fixed canonical identification used after the countable tuple coding. -/
def canonicalHilbertSumEquiv : HilbertSum CanonicalHilbert ≃ₗᵢ[ℂ] CanonicalHilbert :=
  hilbertSumMatrixEquiv.trans (reindexHilbert Nat.pairEquiv)

end
end OperatorCoding

#print axioms OperatorCoding.canonicalHilbertSumEquiv
