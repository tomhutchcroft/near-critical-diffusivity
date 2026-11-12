module

public import NearCritical.ConnectionToSet
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Finite path certificates for the new half-space decomposition argument.
Every certificate forces the actual lattice connection regardless of all outside bits. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Bonds selected along a walk form a finite open certificate. Their underlying
unordered edges belong to the walk, allowing edge-disjointness to be retained. -/
theorem openWalk_certificate {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (w : (openGraph ω).Walk x y) (S : Set (Vertex d))
    (hS : ∀ z ∈ w.support, z ∈ S) :
    ∃ F : Finset (Bond d), (∀ e ∈ F, ω e = true) ∧
      (∀ e ∈ F, s(e.1, bondTip e) ∈ w.edges) ∧
      ∀ θ : Configuration d, (∀ e ∈ F, θ e = true) →
        connectionToSetEvent S x {y} θ := by
  induction w with
  | nil =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro θ _
    exact ⟨hS _ (by simp), _, rfl, hS _ (by simp), SimpleGraph.Reachable.refl _⟩
  | @cons x z y hxz w ih =>
    obtain ⟨F, hopen, hedge, hforce⟩ := ih (fun t ht ↦ hS t (by simp [ht]))
    have hex : ∃ e : Bond d, ω e = true ∧
        ((x = e.1 ∧ z = bondTip e) ∨ (z = e.1 ∧ x = bondTip e)) := hxz
    obtain ⟨e, he, hends⟩ := hex
    have hed : s(e.1, bondTip e) = s(x, z) := by
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    refine ⟨insert e F, ?_, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he
      · exact hopen f hf
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl hed
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (hedge f hf)
    · intro θ hθ
      obtain ⟨hzS, t, ht, hyS, hzy⟩ := hforce θ
        (fun f hf ↦ hθ f (Finset.mem_insert_of_mem hf))
      have hty : t = y := ht
      subst t
      refine ⟨hS _ (by simp), y, rfl, hyS, ?_⟩
      apply SimpleGraph.Reachable.trans _ hzy
      apply SimpleGraph.Adj.reachable
      exact ⟨⟨e, hθ e (Finset.mem_insert_self _ _), hends⟩, hS _ (by simp), hzS⟩

/-- Two actual edge-disjoint open walks yield standard finite-forcing disjoint
occurrence; no values outside the certificates are fixed. -/
theorem disjointOpenWalks_occurrence {d : ℕ} {ω : Configuration d}
    {x u y v : Vertex d} (w : (openGraph ω).Walk x u) (q : (openGraph ω).Walk y v)
    (hdis : w.edges.Disjoint q.edges) (S T A B : Set (Vertex d))
    (hwS : ∀ z ∈ w.support, z ∈ S) (hqT : ∀ z ∈ q.support, z ∈ T)
    (huA : u ∈ A) (hvB : v ∈ B) :
    DisjointOccurrence (connectionToSetEvent S x A) (connectionToSetEvent T y B) ω := by
  obtain ⟨F, hopenF, hedgeF, hF⟩ := openWalk_certificate w S hwS
  obtain ⟨H, hopenH, hedgeH, hH⟩ := openWalk_certificate q T hqT
  refine ⟨F, H, F.finite_toSet, H.finite_toSet, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun e heF heH ↦
      List.disjoint_left.mp hdis (hedgeF e heF) (hedgeH e heH))
  · intro θ hθ
    obtain ⟨hxS, z, hz, hzS, hp⟩ := hF θ (fun e he ↦ (hθ e he).trans (hopenF e he))
    have hzu : z = u := hz
    subst z
    exact ⟨hxS, u, huA, hzS, hp⟩
  · intro θ hθ
    obtain ⟨hyT, z, hz, hzT, hp⟩ := hH θ (fun e he ↦ (hθ e he).trans (hopenH e he))
    have hzv : z = v := hz
    subst z
    exact ⟨hyT, v, hvB, hzT, hp⟩

/-- Splitting a simple path at any visited vertex gives disjoint finite bond
certificates, allowing different domains for the two path pieces. -/
theorem simplePath_split_occurrence {d : ℕ} {ω : Configuration d} {x y u : Vertex d}
    (w : (openGraph ω).Walk x y) (hw : w.IsPath) (hu : u ∈ w.support)
    (S T B : Set (Vertex d))
    (hS : ∀ z ∈ (w.takeUntil u hu).support, z ∈ S)
    (hT : ∀ z ∈ (w.dropUntil u hu).support, z ∈ T) (hy : y ∈ B) :
    DisjointOccurrence (connectionToSetEvent S x {u}) (connectionToSetEvent T u B) ω :=
  disjointOpenWalks_occurrence (w.takeUntil u hu) (w.dropUntil u hu)
    (hw.isTrail.disjoint_edges_takeUntil_dropUntil hu) S T {u} B hS hT rfl hy

/-- A restricted walk visits only its domain, including a zero-length walk
when its initial endpoint belongs to the domain. -/
lemma restrictedWalk_support {d : ℕ} {ω : Configuration d} {S : Set (Vertex d)}
    {x y : Vertex d} (w : (restrictedGraph ω S).Walk x y) (hx : x ∈ S) :
    ∀ z ∈ w.support, z ∈ S := by
  induction w with
  | nil => simpa using hx
  | @cons x z y hadj w ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hx
    · exact ih hadj.2.2 t ht

/-- The minimum-height decomposition used in source Step 2, stated for an
arbitrary domain and actual target set. Both pieces are restricted above the
selected minimum, with standard disjoint finite forcing certificates. -/
theorem connectionToSet_minimum_split {d : ℕ} {ω : Configuration d}
    (S B : Set (Vertex d)) (x : Vertex d) (i : Fin d)
    (hω : ω ∈ connectionToSetEvent S x B) :
    ∃ u : Vertex d, u ∈ S ∧ u i ≤ x i ∧
      DisjointOccurrence
        (connectionToSetEvent (S ∩ {z | u i ≤ z i}) x {u})
        (connectionToSetEvent (S ∩ {z | u i ≤ z i}) u B) ω := by
  obtain ⟨hx, y, hyB, _, ⟨w⟩⟩ := hω
  have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h ↦ h.1
  let p : (openGraph ω).Walk x y := (w.toPath : (restrictedGraph ω S).Walk x y).mapLe hle
  have hp : p.IsPath := w.toPath.property.mapLe _
  have hpS : ∀ z ∈ p.support, z ∈ S := by
    simpa only [p, SimpleGraph.Walk.support_mapLe_eq_support] using
      restrictedWalk_support (w.toPath : (restrictedGraph ω S).Walk x y) hx
  obtain ⟨u, hu, hmin⟩ := p.support.toFinset.exists_min_image (fun z ↦ z i)
    ⟨x, by simp⟩
  have hu' : u ∈ p.support := List.mem_toFinset.mp hu
  have hmin' : ∀ z ∈ p.support, u i ≤ z i :=
    fun z hz ↦ hmin z (List.mem_toFinset.mpr hz)
  refine ⟨u, hpS u hu', hmin' x p.start_mem_support, ?_⟩
  apply simplePath_split_occurrence p hp hu' _ _ B _ _ hyB
  · intro z hz
    have hz' := p.support_takeUntil_subset_support hu' hz
    exact ⟨hpS z hz', hmin' z hz'⟩
  · intro z hz
    have hz' := p.support_dropUntil_subset_support hu' hz
    exact ⟨hpS z hz', hmin' z hz'⟩

/-- Half-space form of the minimum decomposition: the selected height lies
between the boundary and the starting height. This includes empty path pieces. -/
theorem halfSpace_connection_minimum_split {d : ℕ} {ω : Configuration d}
    (i : Fin d) (a : ℤ) (x : Vertex d) (B : Set (Vertex d))
    (hω : ω ∈ connectionToSetEvent {z | a ≤ z i} x B) :
    ∃ u : Vertex d, a ≤ u i ∧ u i ≤ x i ∧
      DisjointOccurrence (connectionToSetEvent {z | u i ≤ z i} x {u})
        (connectionToSetEvent {z | u i ≤ z i} u B) ω := by
  obtain ⟨u, hu, hux, hdis⟩ := connectionToSet_minimum_split {z | a ≤ z i} B x i hω
  change a ≤ u i at hu
  have heq : {z : Vertex d | a ≤ z i} ∩ {z | u i ≤ z i} = {z | u i ≤ z i} := by
    ext z
    constructor
    · exact fun hz ↦ hz.2
    · intro hz
      exact ⟨hu.trans hz, hz⟩
  exact ⟨u, hu, hux, by simpa only [heq] using hdis⟩

end NearCritical
