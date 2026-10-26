import BoundedGraphNull
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Encodable.Basic

/-! The full binary free-group shift and its four-generator Borel graph.
The full shift is used, including points with stabilizers. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkShift

abbrev Group := FreeGroup (Fin 2)
abbrev Point := Group → Bool
abbrev Letter := Fin 2 × Bool
abbrev Alphabet := Option Letter

def shift (g : Group) (x : Point) : Point := fun h => x (g⁻¹ * h)

@[simp] lemma shift_one (x : Point) : shift 1 x = x := by ext h; simp [shift]

lemma shift_mul (g h : Group) (x : Point) : shift g (shift h x) = shift (g * h) x := by
  ext k
  simp only [shift, mul_inv_rev, mul_assoc]

theorem continuous_shift (g : Group) : Continuous (shift g) := by
  apply continuous_pi
  intro h
  exact continuous_apply _

def letterGroup (a : Letter) : Group := if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹
def reverseLetter (a : Letter) : Letter := (a.1, !a.2)

lemma letterGroup_reverse (a : Letter) : letterGroup (reverseLetter a) = (letterGroup a)⁻¹ := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [letterGroup, reverseLetter]

def graph : SimpleGraph Point where
  Adj x y := x ≠ y ∧ ∃ a : Letter, shift (letterGroup a) x = y
  symm := by
    intro x y h
    obtain ⟨hne, a, ha⟩ := h
    refine ⟨hne.symm, reverseLetter a, ?_⟩
    rw [← ha, letterGroup_reverse, shift_mul, inv_mul_cancel, shift_one]
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma reachable_letter (a : Letter) (x : Point) : graph.Reachable x (shift (letterGroup a) x) := by
  by_cases heq : x = shift (letterGroup a) x
  · rw [← heq]
  · exact (show graph.Adj x (shift (letterGroup a) x) from ⟨heq, a, rfl⟩).reachable

theorem reachable_shift (g : Group) : ∀ x : Point, graph.Reachable x (shift g x) := by
  induction g using FreeGroup.induction_on with
  | C1 => intro x; simpa using (SimpleGraph.Reachable.refl (G := graph) x)
  | of i =>
      intro x
      simpa only [letterGroup, if_pos rfl] using reachable_letter (i, true) x
  | inv_of i ih =>
      intro x
      simpa only [letterGroup, Bool.false_eq_true, if_false] using reachable_letter (i, false) x
  | mul g h hg hh =>
      intro x
      exact (hh x).trans (by simpa only [shift_mul] using hg (shift h x))

theorem reachable_iff_shift (x y : Point) : graph.Reachable x y ↔ ∃ g : Group, y = shift g x := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨1, (shift_one _).symm⟩
    | @cons u v z hadj w ih =>
        obtain ⟨a, ha⟩ := hadj.2
        obtain ⟨g, hg⟩ := ih
        exact ⟨g * letterGroup a, by rw [hg, ← ha, shift_mul]⟩
  · rintro ⟨g, rfl⟩
    exact reachable_shift g x

instance groupCountable : Countable Group := by unfold Group FreeGroup; infer_instance
local instance : Encodable Group := Encodable.ofCountable Group

def cantorCode (x : Point) (n : ℕ) : Bool :=
  match Encodable.decode (α := Group) n with
  | none => false
  | some g => x g

theorem measurable_cantorCode : Measurable cantorCode := by
  apply measurable_pi_lambda
  intro n
  cases hdecode : Encodable.decode (α := Group) n with
  | none => simpa only [cantorCode, hdecode] using (measurable_const : Measurable (fun _ : Point => false))
  | some g => simpa only [cantorCode, hdecode] using (measurable_pi_apply g : Measurable (fun x : Point => x g))

theorem cantorCode_injective : Function.Injective cantorCode := by
  intro x y h
  funext g
  have hc := congrFun h (Encodable.encode g)
  simpa only [cantorCode, Encodable.encodek] using hc

end BenchmarkShift

#print axioms BenchmarkShift.reachable_iff_shift
#print axioms BenchmarkShift.cantorCode_injective
