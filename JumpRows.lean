import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Order.Filter.CountableInter
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-! The common category lemma used in both jump-obstruction proofs of
`Benchmark.tex`.  This file proves the category and row-support argument.
It does not assert either of the two obstruction theorems: obtaining the
local row hypothesis for their two concrete source spaces is separate work. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*}

/-- The Friedman--Stanley jump records precisely the countable set of row classes. -/
def Jump (R : Y → Y → Prop) (u v : ℕ → Y) : Prop :=
  (∀ k, ∃ l, R (u k) (v l)) ∧ (∀ l, ∃ k, R (u k) (v l))

def Homomorphism (E : X → X → Prop) (R : Y → Y → Prop) (F : X → Y) : Prop :=
  ∀ x y, E x y → R (F x) (F y)

variable [TopologicalSpace X]

/-- Generic ergodicity, stated for invariant sets with the Baire property. -/
def GenericallyErgodic (E : X → X → Prop) : Prop :=
  ∀ s : Set X, BaireMeasurableSet s →
    (∀ x y, E x y → (x ∈ s ↔ y ∈ s)) →
    IsMeagre s ∨ s ∈ residual X

/-- Local constancy is comeagerness relative to the open set, expressed as
an eventual implication in the ambient residual filter. -/
def LocallyGenericallyConstantRows (R : Y → Y → Prop)
    (F : X → ℕ → Y) : Prop :=
  ∀ k (A : Set X), IsOpen A → A.Nonempty →
    ∃ O : Set X, ∃ a : Y, IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧
      ∀ᶠ x in residual X, x ∈ O → R (F x k) a

/-- A countable basis turns the local row hypothesis into a single countable
family containing all row classes at comeager many source points. -/
theorem countable_row_representatives [SecondCountableTopology X]
    (R : Y → Y → Prop) (F : X → ℕ → Y)
    (hloc : LocallyGenericallyConstantRows R F) :
    ∃ a : ℕ × countableBasis X → Y,
      ∀ᶠ x in residual X, ∀ k, ∃ r, R (F x k) (a r) := by
  classical
  choose O a hOo hOn hOs hOres using fun (k : ℕ) (B : countableBasis X) =>
    hloc k B (isOpen_of_mem_countableBasis B.property)
      (nonempty_of_mem_countableBasis B.property)
  have hDense (k : ℕ) : Dense (⋃ B, O k B) := by
    apply dense_iff_inter_open.2
    intro U hU hUn
    obtain ⟨x, hx⟩ := hUn
    obtain ⟨B, hB, _hxB, hBU⟩ :=
      (isBasis_countableBasis X).exists_subset_of_mem_open hx hU
    obtain ⟨y, hy⟩ := hOn k ⟨B, hB⟩
    exact ⟨y, hBU (hOs k ⟨B, hB⟩ hy), mem_iUnion.2 ⟨⟨B, hB⟩, hy⟩⟩
  have hCover : ∀ᶠ x in residual X, ∀ k, x ∈ ⋃ B, O k B :=
    eventually_countable_forall.2 fun k =>
      residual_of_dense_open (isOpen_iUnion (hOo k)) (hDense k)
  have hGood : ∀ᶠ x in residual X, ∀ r : ℕ × countableBasis X,
      x ∈ O r.1 r.2 → R (F x r.1) (a r.1 r.2) :=
    eventually_countable_forall.2 fun r => hOres r.1 r.2
  refine ⟨fun r => a r.1 r.2, ?_⟩
  filter_upwards [hCover, hGood] with x hx hg
  intro k
  obtain ⟨B, hB⟩ := mem_iUnion.1 (hx k)
  exact ⟨(k, B), hg (k, B) hB⟩

/-- Jump homomorphisms preserve the membership of every fixed target class
in their countable set of row classes. -/
theorem row_support_invariant (R : Y → Y → Prop) (hR : Equivalence R)
    (E : X → X → Prop) (F : X → ℕ → Y)
    (hF : Homomorphism E (Jump R) F) (a : Y) :
    ∀ x y, E x y →
      ((∃ k, R (F x k) a) ↔ ∃ k, R (F y k) a) := by
  intro x y hxy
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := (hF x y hxy).1 k
    exact ⟨l, hR.trans (hR.symm hl) hk⟩
  · rintro ⟨l, hl⟩
    obtain ⟨k, hk⟩ := (hF x y hxy).2 l
    exact ⟨k, hR.trans hk hl⟩

/-- Countably many Baire invariant coordinates are simultaneously constant
on one comeager set. -/
theorem invariant_coordinates_constant {ι : Type*} [Countable ι]
    (E : X → X → Prop) (hE : GenericallyErgodic E)
    (P : ι → X → Prop)
    (hP : ∀ i, BaireMeasurableSet {x | P i x})
    (hInv : ∀ i x y, E x y → (P i x ↔ P i y)) :
    ∃ b : ι → Bool, ∀ᶠ x in residual X, ∀ i, P i x ↔ b i = true := by
  classical
  have hOne (i : ι) : ∃ b : Bool,
      ∀ᶠ x in residual X, P i x ↔ b = true := by
    rcases hE {x | P i x} (hP i) (hInv i) with hm | hr
    · refine ⟨false, ?_⟩
      filter_upwards [hm] with x hx
      simp only [mem_compl_iff, mem_setOf_eq] at hx
      simp [hx]
    · refine ⟨true, ?_⟩
      filter_upwards [hr] with x hx
      simpa using hx
  choose b hb using hOne
  exact ⟨b, eventually_countable_forall.2 hb⟩

/-- The countable-class part of the row lemma, after the countable basis
argument has produced representatives. -/
theorem generically_constant_of_representatives {ι : Type*} [Countable ι]
    [Nonempty X] [BaireSpace X]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (F : X → ℕ → Y) (hF : Homomorphism E (Jump R) F)
    (hE : GenericallyErgodic E) (a : ι → Y)
    (hRep : ∀ᶠ x in residual X, ∀ k, ∃ r, R (F x k) (a r))
    (hBaire : ∀ r, BaireMeasurableSet {x | ∃ k, R (F x k) (a r)}) :
    ∃ v : ℕ → Y, ∀ᶠ x in residual X, Jump R (F x) v := by
  obtain ⟨b, hb⟩ := invariant_coordinates_constant E hE
    (fun r x => ∃ k, R (F x k) (a r)) hBaire
    (fun r => row_support_invariant R hR E F hF (a r))
  obtain ⟨x₀, hxRep, hxBool⟩ := (dense_of_mem_residual (hRep.and hb)).nonempty
  refine ⟨F x₀, ?_⟩
  filter_upwards [hRep, hb] with x hxR hxb
  constructor
  · intro k
    obtain ⟨r, hr⟩ := hxR k
    have hrb : b r = true := (hxb r).mp ⟨k, hr⟩
    obtain ⟨l, hl⟩ := (hxBool r).mpr hrb
    exact ⟨l, hR.trans hr (hR.symm hl)⟩
  · intro l
    obtain ⟨r, hr⟩ := hxRep l
    have hrb : b r = true := (hxBool r).mp ⟨l, hr⟩
    obtain ⟨k, hk⟩ := (hxb r).mpr hrb
    exact ⟨k, hR.trans hk (hR.symm hr)⟩

/-- Borel row maps and a Borel target relation give Baire measurable
class-support coordinates, as required by generic ergodicity. -/
theorem row_support_baire [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (R : Y → Y → Prop) (hR : MeasurableSet {p : Y × Y | R p.1 p.2})
    (F : X → ℕ → Y) (hF : Measurable F) (a : Y) :
    BaireMeasurableSet {x | ∃ k, R (F x k) a} := by
  apply MeasurableSet.baireMeasurableSet
  have hOne (k : ℕ) : MeasurableSet {x | R (F x k) a} :=
    hR.preimage (((measurable_pi_apply k).comp hF).prodMk measurable_const)
  simpa only [setOf_exists] using MeasurableSet.iUnion hOne

/-- Lemma `rows` of the manuscript, with its Borel and topology assumptions
made explicit. This proves the common row-to-jump category implication in full. -/
theorem locally_constant_rows_imp_constant_jump
    [SecondCountableTopology X] [Nonempty X] [BaireSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hRBorel : MeasurableSet {p : Y × Y | R p.1 p.2})
    (F : X → ℕ → Y) (hFmeas : Measurable F)
    (hF : Homomorphism E (Jump R) F) (hE : GenericallyErgodic E)
    (hloc : LocallyGenericallyConstantRows R F) :
    ∃ v : ℕ → Y, ∀ᶠ x in residual X, Jump R (F x) v := by
  obtain ⟨a, ha⟩ := countable_row_representatives R F hloc
  exact generically_constant_of_representatives E R hR F hF hE a ha
    (fun r => row_support_baire R hRBorel F hFmeas (a r))

theorem jump_equivalence (R : Y → Y → Prop) (hR : Equivalence R) :
    Equivalence (Jump R) := by
  constructor
  · intro x
    exact ⟨fun k => ⟨k, hR.refl _⟩, fun k => ⟨k, hR.refl _⟩⟩
  · intro x y hxy
    exact ⟨fun k => (hxy.2 k).imp fun l hl => hR.symm hl,
      fun l => (hxy.1 l).imp fun k hk => hR.symm hk⟩
  · intro x y z hxy hyz
    constructor
    · intro k
      obtain ⟨l, hl⟩ := hxy.1 k
      obtain ⟨m, hm⟩ := hyz.1 l
      exact ⟨m, hR.trans hl hm⟩
    · intro m
      obtain ⟨l, hl⟩ := hyz.2 m
      obtain ⟨k, hk⟩ := hxy.2 l
      exact ⟨k, hR.trans hk hl⟩

/-- A relation with meager classes cannot have a reduction that is constant
modulo the target on a comeager set. No descriptive-set-theoretic obstruction
is assumed in this implication. -/
theorem not_reduction_of_generic_constancy [Nonempty X] [BaireSpace X]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hClasses : ∀ x, IsMeagre {y | E y x})
    (F : X → Y) (hConst : ∃ v, ∀ᶠ x in residual X, R (F x) v) :
    ¬ (∀ x y, E x y ↔ R (F x) (F y)) := by
  intro hRed
  obtain ⟨v, hv⟩ := hConst
  obtain ⟨x₀, hx₀⟩ := (dense_of_mem_residual hv).nonempty
  have hClass : {y | R (F y) v} ⊆ {y | E y x₀} := by
    intro y hy
    exact (hRed y x₀).mpr (hR.trans hy (hR.symm hx₀))
  exact not_isMeagre_of_mem_residual hv ((hClasses x₀).mono hClass)

/-- The general reduction obstruction after local row constancy and
generic ergodicity have been proved for a concrete source. -/
theorem not_borel_reduction_of_local_rows
    [SecondCountableTopology X] [Nonempty X] [BaireSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hRBorel : MeasurableSet {p : Y × Y | R p.1 p.2})
    (hE : GenericallyErgodic E) (hClasses : ∀ x, IsMeagre {y | E y x})
    (hLocal : ∀ F : X → ℕ → Y, Measurable F →
      Homomorphism E (Jump R) F → LocallyGenericallyConstantRows R F) :
    ¬ ∃ F : X → ℕ → Y, Measurable F ∧
      ∀ x y, E x y ↔ Jump R (F x) (F y) := by
  rintro ⟨F, hFm, hRed⟩
  have hF : Homomorphism E (Jump R) F := fun x y h => (hRed x y).mp h
  have hConst := locally_constant_rows_imp_constant_jump E R hR hRBorel F hFm hF hE
    (hLocal F hFm hF)
  exact not_reduction_of_generic_constancy E (Jump R) (jump_equivalence R hR)
    hClasses F hConst hRed

#print axioms locally_constant_rows_imp_constant_jump
#print axioms not_borel_reduction_of_local_rows

end BenchmarkJump
