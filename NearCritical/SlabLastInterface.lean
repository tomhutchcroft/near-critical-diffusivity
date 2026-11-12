module
public import NearCritical.HalfSpaceLastVisit
public import NearCritical.SlabPioneerConvolution

/-! Source critical Case(b) in lem.A.upperbound.inhomo: remove the p-rate
interface bond before identifying the remaining suffix with the q-law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- An upward unit height step of an actual open lattice bond is precisely
translation by the positive coordinate unit vector. -/
lemma openGraph_adj_eq_positive_step {d : ℕ} {ω : Configuration d}
    {x y : Vertex d} (hxy : (openGraph ω).Adj x y) (i : Fin d)
    (hy : y i = x i+1) : y = x+Pi.single i 1 := by
  obtain ⟨e,_he,hends⟩ := hxy
  have haxis : e.2 = i := by
    by_contra hne
    have ht : bondTip e i = e.1 i := by
      simp [bondTip,Function.update_of_ne (Ne.symm hne)]
    rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · funext a
    by_cases hai : a = i
    · subst a
      simp [bondTip,haxis]
    · simp [bondTip,haxis,hai]
  · have ht : bondTip e i = e.1 i+1 := by simp [bondTip,haxis]
    omega

/-- Last-interface decomposition with the crossing bond omitted from BOTH
certificates. The suffix starts at v+e_i and lies strictly above the interface;
no rate law, independence or probability bound is assumed. -/
theorem connectionToSet_last_interface_split {d : ℕ} {ω : Configuration d}
    (S B : Set (Vertex d)) (x : Vertex d) (i : Fin d) (m : ℤ)
    (hx : x i ≤ m) (hB : ∀ y ∈ B, m < y i)
    (hω : ω ∈ connectionToSetEvent S x B) :
    ∃ v : Vertex d, v i = m ∧ DisjointOccurrence
      (connectionToSetEvent S x {v})
      (connectionToSetEvent (S ∩ {z | m+1 ≤ z i}) (v+Pi.single i 1) B) ω := by
  obtain ⟨hxS,y,hyB,_hyS,⟨w⟩⟩ := hω
  have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1
  let r : (openGraph ω).Walk x y := (w.toPath : (restrictedGraph ω S).Walk x y).mapLe hle
  have hr : r.IsPath := w.toPath.property.mapLe _
  have hrS : ∀ z ∈ r.support, z ∈ S := by
    simpa only [r,SimpleGraph.Walk.support_mapLe_eq_support] using
      restrictedWalk_support (w.toPath : (restrictedGraph ω S).Walk x y) hxS
  obtain ⟨v,p,q,hpq,hvm,hlast⟩ := walk_last_visit r (fun z => z i = m)
    (openWalk_visits_height r i m hx (hB y hyB).le)
  have hdis : p.edges.Disjoint q.edges :=
    ((SimpleGraph.Walk.isTrail_append p q).mp (hpq.symm ▸ hr.isTrail)).2.2
  have hpS : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    apply hrS z
    rw [← hpq]
    exact p.support_subset_support_append_left q hz
  have hqS : ∀ z ∈ q.support, z ∈ S := by
    intro z hz
    apply hrS z
    rw [← hpq]
    exact p.support_subset_support_append_right q hz
  cases q with
  | nil => have := hB y hyB; omega
  | @cons v z y hvz q =>
    have hstrict : ∀ t ∈ q.support, m < t i :=
      openWalk_above_of_avoids_height q i m (hB y hyB).le (by simpa using hlast)
    have hstep : z i = v i+1 := by
      have hz := hstrict z q.start_mem_support
      have hb := (openGraph_adj_height_bounds hvz i).2
      omega
    have hzv : z = v+Pi.single i 1 := openGraph_adj_eq_positive_step hvz i hstep
    have hdis' : p.edges.Disjoint q.edges := by
      apply List.disjoint_left.mpr
      intro e hep heq
      apply List.disjoint_left.mp hdis hep
      simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]
      exact Or.inr heq
    have hqT : ∀ t ∈ q.support, t ∈ S ∩ {z | m+1 ≤ z i} := by
      intro t ht
      refine ⟨hqS t (by simp [ht]),?_⟩
      change m+1 ≤ t i
      have hheight := hstrict t ht
      omega
    refine ⟨v,hvm,?_⟩
    have hocc := disjointOpenWalks_occurrence p q hdis' S
      (S ∩ {z | m+1 ≤ z i}) {v} B hpS hqT rfl hyB
    simpa only [hzv] using hocc

/-- Literal source slab specialization. In particular no interface bond is
erroneously assigned the strict-upper-phase law. -/
theorem slab_connection_last_interface_split {d : ℕ} {ω : Configuration d}
    (i : Fin d) (n m : ℤ) (x y : Vertex d) (hm : 0 ≤ m)
    (hx : x i ≤ m) (hy : m < y i)
    (hω : ω ∈ connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) :
    ∃ v : Vertex d, v i = m ∧ DisjointOccurrence
      (connectionToSetEvent (finiteHeightSlab i 0 n) x {v})
      (connectionToSetEvent (finiteHeightSlab i (m+1) n) (v+Pi.single i 1) {y}) ω := by
  have hdom : finiteHeightSlab i 0 n ∩ {z | m+1 ≤ z i} =
      finiteHeightSlab i (m+1) n := by
    ext z
    change ((0 ≤ z i ∧ z i ≤ n) ∧ m+1 ≤ z i) ↔ (m+1 ≤ z i ∧ z i ≤ n)
    omega
  simpa only [hdom] using connectionToSet_last_interface_split
    (finiteHeightSlab i 0 n) {y} x i m hx (by intro z hz; cases hz; exact hy) hω

end NearCritical
