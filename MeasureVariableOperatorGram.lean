import MeasureVariableGramSchmidt

/-! Matrix measurability survives the varying-fiber Gram–Schmidt process
for any operator family with measurable fundamental matrix entries. The
operator images need not lie in a finite span of the fundamental family. -/

open MeasureTheory InnerProductSpace Set

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : S → Type*} [∀ s, NormedAddCommGroup (E s)] [∀ s, InnerProductSpace ℂ (E s)]

theorem FiniteBorelSection.operator_inner_measurable {f : ∀ s, ℕ → E s}
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ i j, Measurable (fun s => inner ℂ (f s i) (T s (f s j))))
    {v w : ∀ s, E s} (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    Measurable (fun s => inner ℂ (v s) (T s (w s))) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  have heq : (fun s => inner ℂ (v s) (T s (w s))) = fun s =>
      ∑ i : I, ∑ l : J, d s l * ((starRingEnd ℂ) (c s i) *
        inner ℂ (f s (j i)) (T s (f s (k l)))) := by
    funext s
    rw [hv s, hw s, map_sum, sum_inner]
    simp only [map_smul, inner_sum, inner_smul_left, inner_smul_right]
  rw [heq]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro l hl
  exact (hd l).mul ((Complex.continuous_conj.measurable.comp (hc i)).mul (hT (j i) (k l)))

theorem variableGramSchmidtNormed_matrix_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ i j, Measurable (fun s => inner ℂ (f s i) (T s (f s j)))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (gramSchmidtNormed ℂ (f s) i)
      (T s (gramSchmidtNormed ℂ (f s) j))) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram i).operator_inner_measurable T hT
    (variableGramSchmidtNormed_finiteBorelSection f hgram j)

set_option maxHeartbeats 800000 in
theorem variableSelectedGramSchmidt_matrix_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ i j, Measurable (fun s => inner ℂ (f s i) (T s (f s j)))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (variableSelectedGramSchmidt f s i)
      (T s (variableSelectedGramSchmidt f s j))) := by
  classical
  have hI (n : ℕ) : Measurable (fun s => Nat.nth (fun k => gramSchmidtNormed ℂ (f s) k ≠ 0) n) :=
    measurable_nat_nth _ (variableGramSchmidtNormed_nonzero_measurableSet f hgram) hinf n
  have hm : Measurable (fun p : S × (ℕ × ℕ) =>
      inner ℂ (gramSchmidtNormed ℂ (f p.1) p.2.1)
        (T p.1 (gramSchmidtNormed ℂ (f p.1) p.2.2))) :=
    measurable_from_prod_countable_left (fun ij =>
      variableGramSchmidtNormed_matrix_measurable f hgram T hT ij.1 ij.2)
  exact hm.comp (measurable_id.prodMk ((hI i).prodMk (hI j)))

end MeasureUnitary

#print axioms MeasureUnitary.variableSelectedGramSchmidt_matrix_measurable
