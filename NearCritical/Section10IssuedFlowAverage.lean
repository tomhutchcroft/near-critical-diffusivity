import NearCritical.Section10ConditionalFlow
import NearCritical.Section10OverlapEnergy
import NearCritical.Section10IssuedPathSupport
import NearCritical.SelectedNestChain
import NearCritical.HalfSpaceArmGeometry
import NearCritical.ExternalLawBridge

section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

/-- Read the concatenation of an internally confined selected trace in the
induced graph of the issued box. The terminal bond is appended separately. -/
theorem selected_trace_exists_issued_internal_walk {d n : ℕ} {ι : Type*}
    {ω : Configuration d} {U : Finset (Vertex d)} {A B : ℝ}
    (tr : SelectedNestTrace d ι ω (U : Set (Vertex d)) A B n)
    {x y : ↥(U : Set (Vertex d))}
    (hx : x.val ∈ tr.interfaceSites 0 (tr.representative 0))
    (hy : y.val ∈ tr.interfaceSites n (tr.representative n)) :
    ∃ v : ((openGraph ω).induce (U : Set (Vertex d))).Walk x y,
      (v.length : ℝ) ≤ ((n : ℝ) + 1) * A + (n : ℝ) * B := by
  obtain ⟨w, hw⟩ := microscopicChain_exists_walk (tr.geometry hx hy)
  have hle : restrictedGraph ω (U : Set (Vertex d)) ≤ openGraph ω :=
    fun _ _ h => h.1
  let u := w.mapLe hle
  have hu : ∀ z ∈ u.support, z ∈ (U : Set (Vertex d)) := by
    simpa only [u, SimpleGraph.Walk.support_mapLe_eq_support] using
      restrictedWalk_support w x.property
  let v := u.induce (U : Set (Vertex d)) hu
  have hvlen : v.length = u.length := by
    calc
      v.length = (v.map (SimpleGraph.Embedding.induce (U : Set (Vertex d))).toHom).length :=
        by simp only [SimpleGraph.Walk.length_map]
      _ = u.length := by rw [show v.map (SimpleGraph.Embedding.induce (U : Set (Vertex d))).toHom = u
        from SimpleGraph.Walk.map_induce u hu] <;> rfl
  exact ⟨v, by simpa only [hvlen, u, SimpleGraph.Walk.length_mapLe] using hw⟩

/-- A step to the selected next representative supplies the actual bridge
walk. Its edges avoid both revealed incident sets, including after the
bridge graph is mapped into the open configuration. -/
theorem selected_trace_exists_bridge_walk {d n : ℕ} {ι : Type*}
    {ω : Configuration d} {U : Finset (Vertex d)} {A B : ℝ}
    (tr : SelectedNestTrace d ι ω (U : Set (Vertex d)) A B n)
    (t : ℕ) (ht : t < n) :
    let step := tr.step t ht
    ∃ x ∈ tr.interfaceSites t (tr.representative t),
      ∃ y ∈ tr.interfaceSites (t + 1) (tr.representative (t + 1)),
        ∃ a b, (a, b) ∈ step.pivots ∧
          ∃ v : (restrictedGraph ω (U : Set (Vertex d))).Walk x y,
            (v.length : ℝ) ≤ B ∧
            (∀ e ∈ v.edges, e ∈ (sprinklingBridgeGraph step.leftGraph step.rightGraph a b).edgeSet) ∧
            ∀ e ∈ v.edges, e ∉ exploredEdgeSet step.firstCube step.firstRevealed ∪
              exploredEdgeSet step.lastCube step.lastRevealed := by
  intro step
  obtain ⟨x, hx, y, hy, a, b, hab, hbound, hgraph⟩ :=
    step.bridge (tr.next_representative_offspring ht)
  obtain ⟨w, hw⟩ := hbound.exists_walk
  let v := w.mapLe hgraph
  let hrestrict := microscopicPieceGraph_le_restricted ω (U : Set (Vertex d))
    (exploredEdgeSet step.firstCube step.firstRevealed ∪
      exploredEdgeSet step.lastCube step.lastRevealed)ᶜ
  refine ⟨x, tr.source_in_representative t ht x hx, y,
    tr.target_in_cluster t ht _ y hy, a, b, hab, v.mapLe hrestrict, ?_, ?_, ?_⟩
  · simpa only [v, SimpleGraph.Walk.length_mapLe] using hw
  · intro e he
    apply w.edges_subset_edgeSet
    simpa only [v, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
  · intro e he
    have hv : e ∈ v.edges := by
      simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact microscopicWalk_edges v e hv

/-- Cluster edges in an incident revealed cluster cannot belong to a bridge
that avoids the corresponding examined bond set. -/
theorem incident_cluster_edge_not_in_bridge {d : ℕ}
    (ω : Configuration d) (C Q F : Set (Vertex d))
    (hCQ : C ⊆ Q) (hCF : C ⊆ F)
    {x y : Vertex d} {G : SimpleGraph (Vertex d)}
    (w : G.Walk x y) (havoid : ∀ e ∈ w.edges, e ∉ exploredEdgeSet Q F) :
    Disjoint (restrictedGraph ω C).edgeSet {e | e ∈ w.edges} := by
  apply Set.disjoint_left.mpr
  intro e he hw
  apply havoid e hw
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨_, ha, hb⟩ := (show (restrictedGraph ω C).Adj a b from he)
    exact (pair_mem_exploredEdgeSet Q F a b).mpr ⟨hCQ ha, hCQ hb, Or.inl (hCF ha)⟩

/-- The concatenated walk retains the origin of each physical edge in a
representative cluster or in an actual selected pivot bridge. -/
theorem selected_trace_walk_edge_provenance {d n : ℕ} {ι : Type*}
    {ω : Configuration d} {U : Finset (Vertex d)} {A B : ℝ}
    (tr : SelectedNestTrace d ι ω (U : Set (Vertex d)) A B n)
    {x y : Vertex d}
    (hx : x ∈ tr.interfaceSites 0 (tr.representative 0))
    (hy : y ∈ tr.interfaceSites n (tr.representative n)) :
    ∃ w : (restrictedGraph ω (U : Set (Vertex d))).Walk x y,
      (w.length : ℝ) ≤ ((n : ℝ) + 1) * A + (n : ℝ) * B ∧
      ∀ e ∈ w.edges,
        (∃ t, t ≤ n ∧ e ∈ (restrictedGraph tr.critical (tr.sites t (tr.representative t))).edgeSet) ∨
        ∃ t, ∃ ht : t < n, ∃ a b, (a, b) ∈ (tr.step t ht).pivots ∧
          e ∈ (sprinklingBridgeGraph (tr.step t ht).leftGraph (tr.step t ht).rightGraph a b).edgeSet := by
  have suffix (m t : ℕ) (ht : t + m = n) {z : Vertex d}
      (hz : z ∈ tr.interfaceSites t (tr.representative t)) :
      ∃ w : (restrictedGraph ω (U : Set (Vertex d))).Walk z y,
        (w.length : ℝ) ≤ ((m : ℝ) + 1) * A + (m : ℝ) * B ∧
        ∀ e ∈ w.edges,
          (∃ j, j ≤ n ∧ e ∈ (restrictedGraph tr.critical (tr.sites j (tr.representative j))).edgeSet) ∨
          ∃ j, ∃ hj : j < n, ∃ a b, (a, b) ∈ (tr.step j hj).pivots ∧
            e ∈ (sprinklingBridgeGraph (tr.step j hj).leftGraph (tr.step j hj).rightGraph a b).edgeSet := by
    induction m generalizing t z with
    | zero =>
      have htn : t = n := by omega
      subst t
      obtain ⟨v, hv⟩ := (tr.typical_diameter n le_rfl z hz y hy).exists_walk
      refine ⟨v.mapLe (tr.representativeGraph_le le_rfl), ?_, ?_⟩
      · simpa using hv
      · intro e he
        exact Or.inl ⟨n, le_rfl, v.edges_subset_edgeSet
          (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)⟩
    | succ m ih =>
      have htn : t < n := by omega
      obtain ⟨u, hu, v, hv, a, b, hab, bridge, hbridge, hEdges, _⟩ :=
        selected_trace_exists_bridge_walk tr t htn
      obtain ⟨c, hc⟩ := (tr.typical_diameter t htn.le z hz u hu).exists_walk
      obtain ⟨tail, htail, htailEdges⟩ := ih (t + 1) (by omega) hv
      refine ⟨(c.mapLe (tr.representativeGraph_le htn.le)).append (bridge.append tail), ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_mapLe, Nat.cast_add,
          Nat.cast_one]
        nlinarith
      · intro e he
        simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_mapLe_eq_edges,
          List.mem_append] at he
        rcases he with hcEdge | hbEdge | htEdge
        · exact Or.inl ⟨t, htn.le, c.edges_subset_edgeSet hcEdge⟩
        · exact Or.inr ⟨t, htn, a, b, hab, hEdges e hbEdge⟩
        · exact htailEdges e htEdge
  exact suffix n 0 (Nat.zero_add n) hx

/-- Forgetting the issued vertex labels sends a support edge either to the
underlying internal walk edge or to its single physical exit bond. -/
theorem issued_walk_edge_physical_mem {d : ℕ} {U : Finset (Vertex d)}
    {ω : Configuration d} {x y : ↥(U : Set (Vertex d))}
    (v : ((openGraph ω).induce (U : Set (Vertex d))).Walk x y) (i : Fin d)
    (e : IssuedBond U)
    (he : s((issuedNetwork U).tail e, (issuedNetwork U).head e) ∈
        (v.map (issuedInternalGraphHom U ω)).edges ∨
      s((issuedNetwork U).tail e, (issuedNetwork U).head e) =
        s(internalIssuedVertex U y, issuedExitVertex U y i)) :
    External.bondPair e.val ∈ (v.map (SimpleGraph.Embedding.induce _).toHom).edges ∨
      External.bondPair e.val = External.bondPair (y.val, i) := by
  let forget : DomainVertex U → Vertex d := Subtype.val
  rcases he with he | he
  · left
    rw [SimpleGraph.Walk.edges_map] at he ⊢
    obtain ⟨z, hz, heq⟩ := List.mem_map.mp he
    have h := congrArg (Sym2.map forget) heq
    rw [Sym2.map_map] at h
    exact List.mem_map.mpr ⟨z, hz, h⟩
  · exact Or.inr (congrArg (Sym2.map forget) he)

/-- Count a pair of issued supports by their physical unordered bonds. Each
issued index has a distinct physical bond, including at the terminal face. -/
theorem issued_overlap_card_le_physical {d : ℕ} {U : Finset (Vertex d)}
    (P Q : Finset (IssuedBond U)) (E F : Finset (Sym2 (Vertex d)))
    (hP : ∀ e ∈ P, External.bondPair e.val ∈ E)
    (hQ : ∀ e ∈ Q, External.bondPair e.val ∈ F) :
    (P ∩ Q).card ≤ (E ∩ F).card := by
  let phys : IssuedBond U ↪ Sym2 (Vertex d) :=
    ⟨fun e => External.bondPair e.val,
      fun _ _ h => Subtype.ext (External.bondPair_injective d h)⟩
  rw [← Finset.card_map (f := phys) (s := P ∩ Q)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hz
  obtain ⟨heP, heQ⟩ := Finset.mem_inter.mp he
  exact Finset.mem_inter.mpr ⟨hP e heP, hQ e heQ⟩

/-- Average the issued unit currents of surviving walks. The pair bound uses
their supplied physical edge sets, including the terminal bond. A zero-weight
outcome requires no walk and contributes zero to the average. -/
theorem issued_flow_average_of_surviving_walks {d : ℕ} {I : Type*} [Fintype I]
    (U : Finset (Vertex d)) (ω : Configuration d) (i : Fin d)
    (S T : Set (DomainVertex U)) (hST : Disjoint S T)
    (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (hW : (1 / 2 : ℝ) ≤ ∑ j, w j)
    (edges : I → Finset (Sym2 (Vertex d)))
    (hwalk : ∀ j, w j ≠ 0 →
      ∃ (x y : ↥(U : Set (Vertex d)))
        (v : ((openGraph ω).induce (U : Set (Vertex d))).Walk x y),
        internalIssuedVertex U x ∈ S ∧ issuedExitVertex U y i ∈ T ∧
        ω (y.val, i) = true ∧
        External.bondPair (y.val, i) ∈ edges j ∧
        ∀ e ∈ (v.map (SimpleGraph.Embedding.induce _).toHom).edges, e ∈ edges j) :
    ∃ θ : IssuedBond U → ℝ,
      (issuedNetwork U).IsBoundaryUnitFlow S T θ ∧
      Network.FlowSupported (domainWeights ω) θ ∧
      Network.flowEnergy (domainWeights ω) θ ≤
        4 * (∑ j, ∑ k, w j * w k * ((edges j ∩ edges k).card : ℝ)) := by
  have hcurrents (j : I) :
      ∃ (P : Finset (IssuedBond U)) (θ : IssuedBond U → ℝ),
        (w j ≠ 0 → (issuedNetwork U).IsBoundaryUnitFlow S T θ) ∧
        Network.FlowSupported (domainWeights ω) θ ∧
        (∀ e, |θ e| ≤ if e ∈ P then (1 : ℝ) else 0) ∧
        (∀ e ∈ P, (domainWeights ω : IssuedBond U → ℝ) e = 1) ∧
        (∀ e ∈ P, External.bondPair e.val ∈ edges j) := by
    by_cases hj : w j = 0
    · refine ⟨∅, fun _ => 0, fun h => (h hj).elim, ?_, ?_, ?_, ?_⟩
      · intro e _
        rfl
      · simp
      · simp
      · simp
    · obtain ⟨x, y, v, hx, hy, hExit, hExitMem, hEdges⟩ := hwalk j hj
      obtain ⟨P, θ, hUnit, hSupp, hMag, hOpen, _, _, hSub⟩ :=
        issued_internal_walk_exit_current_support U ω S T hST x y i hx hy v hExit
      refine ⟨P, θ, fun _ => hUnit, hSupp, hMag, hOpen, ?_⟩
      intro e he
      rcases issued_walk_edge_physical_mem v i e (hSub e he) with h | h
      · exact hEdges _ h
      · exact h.symm ▸ hExitMem
  choose P θ hUnit hSupp hMag hOpen hSub using hcurrents
  have hsum : (∑ j, w j) ≠ 0 := by linarith
  refine ⟨Network.normalizedFlow w θ, ?_, ?_, ?_⟩
  · apply Network.isBoundaryUnitFlow_weighted_of_nonzero
    · rw [← Finset.sum_div, div_self hsum]
    · intro j hj
      exact hUnit j (fun h => hj (by simp [h]))
  · exact Network.flowSupported_weighted_of_nonzero _ _ _ (fun j _ => hSupp j)
  · refine (Network.normalized_path_flow_energy_le_four_overlaps _ w θ P hw hW
      (fun j e => ?_) hOpen).trans ?_
    · have h := hMag j e
      by_cases he : e ∈ P j
      · simpa only [if_pos he] using h
      · simpa only [if_neg he] using h
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw j) (hw k))
      have hInter :
          @Inter.inter _ (@Finset.instInter _ (Classical.decEq (IssuedBond U))) (P j) (P k) =
            P j ∩ P k := by
        ext e
        simp only [Finset.mem_inter]
      rw [hInter]
      exact_mod_cast issued_overlap_card_le_physical (P j) (P k) (edges j) (edges k)
        (hSub j) (hSub k)

end NearCritical.Section10
