import PolishGroupTopology

open Set
open scoped Topology

namespace MeasureEquivalenceInvariantGraph

variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)

/-- A separate presentation of H, carrying the graph metric rather than its
possibly incomplete subspace metric from K. -/
def GraphGroup (_r : H → V) : Type _ := H

instance : CommGroup (GraphGroup H r) := inferInstanceAs (CommGroup H)

def inclusion (h : GraphGroup H r) : K := (show H from h)

def graph (h : GraphGroup H r) : K × V := (inclusion H r h, r h)

omit [MetricSpace K] [MetricSpace V] in
theorem inclusion_injective : Function.Injective (inclusion H r) := by
  intro a b hab
  exact Subtype.ext hab

omit [MetricSpace K] [MetricSpace V] in
theorem graph_injective : Function.Injective (graph H r) := by
  intro a b hab
  exact inclusion_injective H r (congrArg Prod.fst hab)

noncomputable instance : MetricSpace (GraphGroup H r) :=
  MetricSpace.induced (graph H r) (graph_injective H r) inferInstance

theorem graph_isometry : Isometry (graph H r) := Isometry.of_dist_eq (fun _ _ => rfl)

theorem inclusion_continuous : Continuous (inclusion H r) :=
  continuous_fst.comp (graph_isometry H r).continuous

theorem feature_continuous : Continuous (fun h : GraphGroup H r => r h) :=
  continuous_snd.comp (graph_isometry H r).continuous

theorem feature_dist_le (a b : GraphGroup H r) : dist (r a) (r b) ≤ dist a b := by
  change dist (r a) (r b) ≤ max (dist (inclusion H r a) (inclusion H r b)) (dist (r a) (r b))
  exact le_max_right _ _

variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))

include hleft in
omit [MetricSpace K] in
theorem feature_inverse (h k : H) : dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k) := by
  have hi := hleft (h * k) h⁻¹ k⁻¹
  have hh : h * k * h⁻¹ = k := by simp
  have hk : h * k * k⁻¹ = h := by group
  rw [hh, hk] at hi
  exact hi.symm.trans (dist_comm _ _)

include hleft in
omit [MetricSpace K] in
theorem feature_mul_bound (a b c d : H) :
    dist (r (a * b)) (r (c * d)) ≤ dist (r a) (r c) + dist (r b) (r d) := by
  calc
    _ ≤ dist (r (a * b)) (r (c * b)) + dist (r (c * b)) (r (c * d)) := dist_triangle _ _ _
    _ = _ := by rw [hleft, mul_comm a b, mul_comm c b, hleft]

include hleft in
theorem graphGroup_topologicalGroup [IsTopologicalGroup K] : IsTopologicalGroup (GraphGroup H r) where
  continuous_mul := by
    apply (graph_isometry H r).isEmbedding.continuous_iff.mpr
    have hr : LipschitzWith 2 (fun p : GraphGroup H r × GraphGroup H r => r (p.1 * p.2)) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      have hb := feature_mul_bound H r hleft p.1 p.2 q.1 q.2
      have h1 := feature_dist_le H r p.1 q.1
      have h2 := feature_dist_le H r p.2 q.2
      have h3 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
      have h4 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
      simp only [NNReal.coe_ofNat, Prod.dist_eq]
      exact hb.trans ((add_le_add h1 h2).trans (by linarith))
    exact (((inclusion_continuous H r).comp continuous_fst).mul
      ((inclusion_continuous H r).comp continuous_snd)).prodMk hr.continuous
  continuous_inv := by
    apply (graph_isometry H r).isEmbedding.continuous_iff.mpr
    have hr : LipschitzWith 1 (fun p : GraphGroup H r => r p⁻¹) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      simp only [NNReal.coe_one, one_mul]
      exact (feature_inverse H r hleft p q).le.trans (feature_dist_le H r p q)
    exact (inclusion_continuous H r).inv.prodMk hr.continuous

theorem graphGroup_complete [CompleteSpace K] [CompleteSpace V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h)))) :
    CompleteSpace (GraphGroup H r) := by
  let : CompleteSpace (Set.range (graph H r)) := hclosed.isComplete.completeSpace_coe
  exact (graph_isometry H r).isometryEquivOnRange.completeSpace

theorem graphGroup_secondCountable [SecondCountableTopology K] [SecondCountableTopology V] :
    SecondCountableTopology (GraphGroup H r) :=
  TopologicalSpace.secondCountableTopology_induced (GraphGroup H r) (K × V) (graph H r)

theorem graphGroup_polish [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h)))) :
    PolishSpace (GraphGroup H r) := by
  let : CompleteSpace (GraphGroup H r) := graphGroup_complete H r hclosed
  let : SecondCountableTopology (GraphGroup H r) := graphGroup_secondCountable H r
  infer_instance

section Presentation

variable [IsTopologicalGroup K] [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h))))
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

include hleft hclosed in
/-- The algebraic identification with any Polish group presentation whose
coordinate inclusion is continuous is a homeomorphism onto the graph group. -/
noncomputable def presentationHomeomorph (e : G ≃* H)
    (he : Continuous (fun g : G => (e g : K))) : G ≃ₜ GraphGroup H r := by
  let : IsTopologicalGroup (GraphGroup H r) := graphGroup_topologicalGroup H r hleft
  let : PolishSpace (GraphGroup H r) := graphGroup_polish H r hclosed
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace (GraphGroup H r) := borel (GraphGroup H r)
  let : BorelSpace (GraphGroup H r) := ⟨rfl⟩
  let e' : G ≃* GraphGroup H r := e
  exact MeasureEquivalenceTopology.inclusionGroupIsoHomeomorph
    (fun g : G => (e g : K)) (inclusion H r) he (inclusion_continuous H r)
    (inclusion_injective H r) e' (fun _ => rfl)

include hleft hclosed in
theorem presentation_graph_embedding (e : G ≃* H)
    (he : Continuous (fun g : G => (e g : K))) :
    Topology.IsEmbedding (fun g : G => ((e g : K), r (e g))) := by
  exact (graph_isometry H r).isEmbedding.comp
    (presentationHomeomorph H r hleft hclosed e he).isEmbedding

end Presentation

end MeasureEquivalenceInvariantGraph

#print axioms MeasureEquivalenceInvariantGraph.graphGroup_topologicalGroup
#print axioms MeasureEquivalenceInvariantGraph.graphGroup_complete
#print axioms MeasureEquivalenceInvariantGraph.graphGroup_polish
#print axioms MeasureEquivalenceInvariantGraph.presentation_graph_embedding
