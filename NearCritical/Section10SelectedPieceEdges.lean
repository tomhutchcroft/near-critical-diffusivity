import NearCritical.Section10IssuedFlowAverage
import NearCritical.Section10TypicalClusters
import NearCritical.Section10TubeGeometry
import NearCritical.Section9FiniteGeometry

section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Retain the actual edge sets of the selected cluster and bridge walks.
The budgets bound these sets individually, so a later overlap charge can use
the length of each chosen piece. -/
theorem selected_trace_walk_piece_edges {d n : ℕ} {ι : Type*}
    {ω : Configuration d} {U : Finset (Vertex d)} {A B : ℝ}
    (tr : SelectedNestTrace d ι ω (U : Set (Vertex d)) A B n)
    {x y : Vertex d}
    (hx : x ∈ tr.interfaceSites 0 (tr.representative 0))
    (hy : y ∈ tr.interfaceSites n (tr.representative n)) :
    ∃ (w : (restrictedGraph ω (U : Set (Vertex d))).Walk x y)
      (clusters bridges : ℕ → Finset (Sym2 (Vertex d))),
      (∀ j ≤ n, ((clusters j).card : ℝ) ≤ A ∧
        (clusters j : Set (Sym2 (Vertex d))) ⊆
          (restrictedGraph tr.critical (tr.sites j (tr.representative j))).edgeSet) ∧
      (∀ j (hj : j < n), ((bridges j).card : ℝ) ≤ B ∧
        (∀ e ∈ bridges j, e ∉ exploredEdgeSet (tr.step j hj).firstCube (tr.step j hj).firstRevealed ∪
          exploredEdgeSet (tr.step j hj).lastCube (tr.step j hj).lastRevealed) ∧
        ∃ a b, (a, b) ∈ (tr.step j hj).pivots ∧
          (bridges j : Set (Sym2 (Vertex d))) ⊆
            (sprinklingBridgeGraph (tr.step j hj).leftGraph (tr.step j hj).rightGraph a b).edgeSet) ∧
      ∀ e ∈ w.edges, (∃ j ≤ n, e ∈ clusters j) ∨ ∃ j < n, e ∈ bridges j := by
  have suffix (m t : ℕ) (ht : t + m = n) {z : Vertex d}
      (hz : z ∈ tr.interfaceSites t (tr.representative t)) :
      ∃ (w : (restrictedGraph ω (U : Set (Vertex d))).Walk z y)
        (clusters bridges : ℕ → Finset (Sym2 (Vertex d))),
        (∀ j, t ≤ j → j ≤ n → ((clusters j).card : ℝ) ≤ A ∧
          (clusters j : Set (Sym2 (Vertex d))) ⊆
            (restrictedGraph tr.critical (tr.sites j (tr.representative j))).edgeSet) ∧
        (∀ j, t ≤ j → ∀ hj : j < n, ((bridges j).card : ℝ) ≤ B ∧
          (∀ e ∈ bridges j, e ∉ exploredEdgeSet (tr.step j hj).firstCube (tr.step j hj).firstRevealed ∪
            exploredEdgeSet (tr.step j hj).lastCube (tr.step j hj).lastRevealed) ∧
          ∃ a b, (a, b) ∈ (tr.step j hj).pivots ∧
            (bridges j : Set (Sym2 (Vertex d))) ⊆
              (sprinklingBridgeGraph (tr.step j hj).leftGraph (tr.step j hj).rightGraph a b).edgeSet) ∧
        ∀ e ∈ w.edges, (∃ j, t ≤ j ∧ j ≤ n ∧ e ∈ clusters j) ∨
          ∃ j, t ≤ j ∧ j < n ∧ e ∈ bridges j := by
    induction m generalizing t z with
    | zero =>
      have htn : t = n := by omega
      subst t
      obtain ⟨c, hc⟩ := (tr.typical_diameter n le_rfl z hz y hy).exists_walk
      refine ⟨c.mapLe (tr.representativeGraph_le le_rfl), fun _ => c.edges.toFinset,
        fun _ => ∅, ?_, ?_, ?_⟩
      · intro j hj hn
        have h : j = n := by omega
        subst j
        have hcard : (c.edges.toFinset.card : ℝ) ≤ c.length := by
          exact_mod_cast (c.edges.toFinset_card_le.trans_eq c.length_edges)
        exact ⟨hcard.trans hc, fun e he => c.edges_subset_edgeSet (List.mem_toFinset.mp he)⟩
      · intro j hj hjn
        omega
      · intro e he
        exact Or.inl ⟨n, le_rfl, le_rfl, List.mem_toFinset.mpr
          (by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he)⟩
    | succ m ih =>
      have htn : t < n := by omega
      obtain ⟨u, hu, v, hv, a, b, hab, bridge, hb, hBridge, hAvoid⟩ :=
        selected_trace_exists_bridge_walk tr t htn
      obtain ⟨c, hc⟩ := (tr.typical_diameter t htn.le z hz u hu).exists_walk
      obtain ⟨tail, clusters, bridges, hClusters, hBridges, hTail⟩ :=
        ih (t + 1) (by omega) hv
      refine ⟨(c.mapLe (tr.representativeGraph_le htn.le)).append (bridge.append tail),
        Function.update clusters t c.edges.toFinset, Function.update bridges t bridge.edges.toFinset,
        ?_, ?_, ?_⟩
      · intro j hj hjn
        by_cases h : j = t
        · subst j
          rw [Function.update_self]
          have hcard : (c.edges.toFinset.card : ℝ) ≤ c.length := by
            exact_mod_cast (c.edges.toFinset_card_le.trans_eq c.length_edges)
          exact ⟨hcard.trans hc, fun e he => c.edges_subset_edgeSet (List.mem_toFinset.mp he)⟩
        · simpa only [Function.update_of_ne h] using hClusters j (by omega) hjn
      · intro j hj hjn
        by_cases h : j = t
        · subst j
          rw [Function.update_self]
          have hcard : (bridge.edges.toFinset.card : ℝ) ≤ bridge.length := by
            exact_mod_cast (bridge.edges.toFinset_card_le.trans_eq bridge.length_edges)
          exact ⟨hcard.trans hb, fun e he => hAvoid e (List.mem_toFinset.mp he),
            a, b, hab, fun e he => hBridge e (List.mem_toFinset.mp he)⟩
        · simpa only [Function.update_of_ne h] using hBridges j (by omega) hjn
      · intro e he
        simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_mapLe_eq_edges,
          List.mem_append] at he
        rcases he with he | he | he
        · exact Or.inl ⟨t, le_rfl, htn.le, by simpa using List.mem_toFinset.mpr he⟩
        · exact Or.inr ⟨t, le_rfl, htn, by simpa using List.mem_toFinset.mpr he⟩
        · rcases hTail e he with ⟨j, hj, hjn, he⟩ | ⟨j, hj, hjn, he⟩
          · exact Or.inl ⟨j, by omega, hjn, by simpa [Function.update_of_ne (show j ≠ t by omega)] using he⟩
          · exact Or.inr ⟨j, by omega, hjn, by simpa [Function.update_of_ne (show j ≠ t by omega)] using he⟩
  obtain ⟨w, clusters, bridges, hc, hb, hcover⟩ := suffix n 0 (Nat.zero_add n) hx
  refine ⟨w, clusters, bridges, fun j hj => hc j (Nat.zero_le j) hj,
    fun j hj => hb j (Nat.zero_le j) hj, ?_⟩
  intro e he
  rcases hcover e he with ⟨j, _, hj, he⟩ | ⟨j, _, hj, he⟩
  · exact Or.inl ⟨j, hj, he⟩
  · exact Or.inr ⟨j, hj, he⟩

/-- A source tube can intersect only its two incident typical cubes. The
coarse spacing is twice the side parameter of the typical cube. -/
theorem coarseTube_disjoint_nonincident_typicalCube {d t : ℕ} (ht : 0 < t)
    (a b : Vertex d) (i : Fin d) (hfirst : b ≠ a) (hlast : b ≠ a + Pi.single i 1) :
    Disjoint (coarseTubeVertices (2 * (t : ℝ)) a i)
      (typicalCube t (fun k => (2 * (t : ℤ)) * b k) : Set (Vertex d)) := by
  apply Set.disjoint_left.mpr
  intro x hx hCube
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have cube_cut (k : Fin d) :
      2 * |(x k : ℝ) - 2 * (t : ℝ) * (b k : ℝ)| < (t : ℝ) := by
    have h := (Finset.mem_filter.mp hCube).2 k
    push_cast at h
    exact h
  have transverse (k : Fin d) (hk : k ≠ i) : b k = a k := by
    have tube := hx k
    simp only [if_neg hk, sub_zero] at tube
    obtain ⟨hL, hU⟩ := abs_lt.mp tube
    have h := cube_cut k
    obtain ⟨hcL, hcU⟩ := abs_lt.mp (show |(x k : ℝ) - 2 * (t : ℝ) * (b k : ℝ)| < (t : ℝ) / 2 by linarith)
    rcases lt_trichotomy (b k) (a k) with hba | heq | hab
    · have hgap : (b k : ℝ) + 1 ≤ (a k : ℝ) := by
        exact_mod_cast (show b k + 1 ≤ a k by omega)
      nlinarith [mul_nonneg htR.le (sub_nonneg.mpr hgap)]
    · exact heq
    · have hgap : (a k : ℝ) + 1 ≤ (b k : ℝ) := by
        exact_mod_cast (show a k + 1 ≤ b k by omega)
      nlinarith [mul_nonneg htR.le (sub_nonneg.mpr hgap)]
  have axial : b i = a i ∨ b i = a i + 1 := by
    have tube := hx i
    simp only [if_pos (rfl : i = i), ite_true] at tube
    obtain ⟨hL, hU⟩ := abs_lt.mp tube
    have h := cube_cut i
    obtain ⟨hcL, hcU⟩ := abs_lt.mp (show |(x i : ℝ) - 2 * (t : ℝ) * (b i : ℝ)| < (t : ℝ) / 2 by linarith)
    by_contra hne
    have hcases : b i + 1 ≤ a i ∨ a i + 2 ≤ b i := by omega
    rcases hcases with hba | hab
    · have hgap : (b i : ℝ) + 1 ≤ (a i : ℝ) := by exact_mod_cast hba
      nlinarith [mul_nonneg htR.le (sub_nonneg.mpr hgap)]
    · have hgap : (a i : ℝ) + 2 ≤ (b i : ℝ) := by exact_mod_cast hab
      nlinarith [mul_nonneg htR.le (sub_nonneg.mpr hgap)]
  rcases axial with heq | heq
  · apply hfirst
    funext k
    by_cases hk : k = i
    · simpa [hk] using heq
    · exact transverse k hk
  · apply hlast
    funext k
    by_cases hk : k = i
    · subst k
      simpa using heq
    · simpa [Pi.single_eq_of_ne hk] using transverse k hk

/-- In coordinates relative to the lower endpoint, the two Section 9
half-tubes form exactly the Section 10 coarse tube. -/
theorem section9_tube_union_mem_coarseTube {d t : ℕ} (ht : 0 < t)
    (a x : Vertex d) (i : Fin d) :
    let center : Vertex d := fun k => (2 * (t : ℤ)) * a k
    x ∈ section9FiniteTube i t (-(5 : ℝ) / 8) (3 / 8) ∪
        section9FiniteTube i t (-(3 : ℝ) / 8) (5 / 8) ↔
      center + x ∈ coarseTubeVertices (2 * (t : ℝ)) a i := by
  intro center
  rw [Finset.mem_union,
    mem_section9FiniteTube i t _ _ (by norm_num) (by norm_num),
    mem_section9FiniteTube i t _ _ (by norm_num) (by norm_num)]
  have htr (k : Fin d) : ((center + x) k : ℝ) =
      2 * (t : ℝ) * (a k : ℝ) + (x k : ℝ) := by
    simp [center, Pi.add_apply, Int.cast_add, Int.cast_mul]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  change (_ ∨ _) ↔ ∀ k : Fin d,
    |16 * ((center + x) k : ℝ) - 16 * (2 * (t : ℝ)) * (a k : ℝ) -
      (if k = i then 8 * (2 * (t : ℝ)) else 0)| <
      if k = i then 5 * (2 * (t : ℝ)) else 3 * (2 * (t : ℝ))
  simp_rw [htr]
  have hcancel (k : Fin d) :
      16 * (2 * (t : ℝ) * (a k : ℝ) + (x k : ℝ)) -
        16 * (2 * (t : ℝ)) * (a k : ℝ) = 16 * (x k : ℝ) := by ring
  simp_rw [hcancel]
  have hshape :
      (∀ k : Fin d, |16 * (x k : ℝ) - (if k = i then 8 * (2 * (t : ℝ)) else 0)| <
        if k = i then 5 * (2 * (t : ℝ)) else 3 * (2 * (t : ℝ))) ↔
      (3 * (t : ℝ) / 8 < (x i : ℝ) ∧ (x i : ℝ) < 13 * (t : ℝ) / 8) ∧
        (∀ k ≠ i, -3 * (t : ℝ) / 8 < (x k : ℝ) ∧ (x k : ℝ) < 3 * (t : ℝ) / 8) := by
    constructor
    · intro h
      have haxis := h i
      simp only [if_pos (rfl : i = i), ite_true] at haxis
      obtain ⟨hl, hu⟩ := abs_lt.mp haxis
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      intro k hk
      have hcross := h k
      simp only [if_neg hk, sub_zero] at hcross
      obtain ⟨hl, hu⟩ := abs_lt.mp hcross
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨⟨hl, hu⟩, hcross⟩ k
      by_cases hk : k = i
      · subst k
        simp only [if_pos (rfl : i = i), ite_true]
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      · simp only [if_neg hk, sub_zero]
        obtain ⟨hl, hu⟩ := hcross k hk
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [hshape]
  unfold sprinklingTube
  constructor
  · rintro (⟨hl, hu, hs⟩ | ⟨hl, hu, hs⟩) <;>
      exact ⟨⟨by linarith, by linarith⟩, hs⟩
  · rintro ⟨⟨hl, hu⟩, hs⟩
    by_cases hx : (x i : ℝ) < 11 * (t : ℝ) / 8
    · exact Or.inl ⟨by linarith, by linarith, hs⟩
    · exact Or.inr ⟨by linarith, by linarith, hs⟩

/-- The graph of a selected bridge stays in the tube when both side regions
and the joining endpoints do. This applies to every edge of its chosen walk. -/
theorem selected_bridge_edges_subset_tube {d : ℕ} {ω : Configuration d}
    {D T : Set (Vertex d)} {B : ℝ} {ι : Type*}
    (step : NestSprinklingStep d ι ω D B)
    (hL : step.leftRegion ⊆ T) (hR : step.rightRegion ⊆ T)
    {a b : Vertex d} (ha : a ∈ T) (hb : b ∈ T) :
    (sprinklingBridgeGraph step.leftGraph step.rightGraph a b).edgeSet ⊆ T.sym2 := by
  intro e he
  rw [sprinklingBridgeGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
  rcases he.1 with hLeft | hPivot | hRight
  · induction e using Sym2.ind with
    | h x y =>
      have h := step.left_deleted ((show step.leftGraph.Adj x y from hLeft))
      exact ⟨hL h.2.1, hL h.2.2.1⟩
  · have heq : e = s(a, b) := hPivot
    subst e
    exact ⟨ha, hb⟩
  · induction e using Sym2.ind with
    | h x y =>
      have h := step.right_deleted ((show step.rightGraph.Adj x y from hRight))
      exact ⟨hR h.2.1, hR h.2.2.1⟩

/-- Cluster and bridge supports are disjoint by spatial separation, or by
the incident reveal deletion when their spatial regions meet. -/
theorem cluster_bridge_support_disjoint {d : ℕ} (critical : Configuration d)
    (C T Q₁ F₁ Q₃ F₃ : Set (Vertex d)) (bridge : Finset (Sym2 (Vertex d)))
    (hTube : (bridge : Set (Sym2 (Vertex d))) ⊆ T.sym2)
    (hAvoid : ∀ e ∈ bridge, e ∉ exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₃ F₃)
    (hCluster : Disjoint C T ∨ (C ⊆ Q₁ ∧ C ⊆ F₁) ∨ (C ⊆ Q₃ ∧ C ⊆ F₃)) :
    Disjoint (restrictedGraph critical C).edgeSet (bridge : Set (Sym2 (Vertex d))) := by
  apply Set.disjoint_left.mpr
  intro e he hb
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨_, hx, hy⟩ := (show (restrictedGraph critical C).Adj x y from he)
    rcases hCluster with hSep | ⟨hQ, hF⟩ | ⟨hQ, hF⟩
    · exact Set.disjoint_left.mp hSep hx (Set.mk_mem_sym2_iff.mp (hTube hb)).1
    · exact hAvoid _ hb (Or.inl ((pair_mem_exploredEdgeSet Q₁ F₁ x y).mpr
        ⟨hQ hx, hQ hy, Or.inl (hF hx)⟩))
    · exact hAvoid _ hb (Or.inr ((pair_mem_exploredEdgeSet Q₃ F₃ x y).mpr
        ⟨hQ hx, hQ hy, Or.inl (hF hx)⟩))

/-- A shared positive-direction exit identifies its issuing vertex, the cube
in a disjoint family containing that vertex, and its actual critical component. -/
theorem common_terminal_edge_identifies_cluster {d : ℕ} {I : Type*}
    (critical : Configuration d) (i : Fin d) (cube : I → Finset (Vertex d))
    (hcube : Pairwise fun j k => Disjoint (cube j) (cube k))
    {j k : I} {C C' : Finset (Vertex d)} {y y' : Vertex d}
    (hC : C ∈ finiteClusterFamily critical (cube j))
    (hC' : C' ∈ finiteClusterFamily critical (cube k))
    (hy : y ∈ C) (hy' : y' ∈ C')
    (he : External.bondPair (y, i) = External.bondPair (y', i)) :
    j = k ∧ C = C' := by
  have hyEq : y = y' := congrArg Prod.fst (External.bondPair_injective d he)
  subst y'
  obtain ⟨root, _, rfl⟩ := (mem_finiteClusterFamily critical (cube j) C).mp hC
  obtain ⟨root', _, rfl⟩ := (mem_finiteClusterFamily critical (cube k) C').mp hC'
  have hjk : j = k := by
    by_contra hne
    exact Finset.disjoint_left.mp (hcube hne)
      (finiteBoxCluster_subset critical (cube j) root hy)
      (finiteBoxCluster_subset critical (cube k) root' hy')
  subst k
  refine ⟨rfl, ?_⟩
  by_contra hne
  exact Finset.disjoint_left.mp (finiteClusterFamily_disjoint critical (cube j) hC hC' hne) hy hy'

end NearCritical.Section10
