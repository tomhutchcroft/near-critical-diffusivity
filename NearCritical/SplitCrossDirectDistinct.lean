module

public import NearCritical.SplitCrossDirectOffReveal

/-! Distinct-cluster realisations (item D of the direct proof of
`SplitCrossInput`, iteration).

Work in a finite vertex domain `U`.

* `doList L`: nested disjoint occurrence of a list of events;
  `doList_probability_le`: `P[doList L] ≤ ∏ P[A]` for increasing events (BK).
* `LocalEv d U`: an increasing event with a root, certified inside the
  `U`-cluster of its root (every occurrence has a finite forcing set of bonds
  with an endpoint in that cluster).
* `distinctLoc U L`: all events of the list occur and the `U`-clusters of their
  roots are pairwise disjoint. `distinct_bk`: `P[distinctLoc U L] ≤ ∏ P[ev]`
  (the certificates are automatically disjoint).
* `connLoc`: a restricted connection `a ↔ b in T`, `T ⊆ U`, as a `LocalEv`;
  `LocalEv.withTarget`: the same event intersected with `root ↔ w in U`.
* `distinct_step`: for a list `L` of stable local events and a new connection,
  `P[distinctLoc L] · P[a ↔ b in T] ≤ P[distinctLoc (new :: L)]`
  `   + Σ_{w ∈ U} P[distinctLoc L, w in the cluster of some root] ·`
  `       P[{a ↔ w in T} ∘ {w ↔ b in T}]`.
* `distinctLoc_inter_mem_subset`: on `distinctLoc (L₁ ++ x :: L₂)`, if `w` is in
  the cluster of `x.root`, then `distinctLoc (L₁ ++ x.withTarget w :: L₂)` holds
  (so `distinct_bk` bounds the error term by a product).
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

/-- Nested disjoint occurrence of a list of events. -/
def doList : List (Set (Configuration d)) → Set (Configuration d)
  | [] => Set.univ
  | [A] => A
  | A :: B :: L => {ω | DisjointOccurrence A (doList (B :: L)) ω}

theorem doList_increasing : ∀ (L : List (Set (Configuration d))),
    (∀ A ∈ L, BK.Increasing A) → BK.Increasing (doList L)
  | [], _ => fun _ _ _ _ => Set.mem_univ _
  | [A], h => h A (by simp)
  | A :: B :: L, h =>
    increasing_disjointOccurrence (h A (by simp))
      (doList_increasing (B :: L) (fun C hC => h C (List.mem_cons_of_mem _ hC)))

theorem doList_probability_le (p : unitInterval) : ∀ (L : List (Set (Configuration d))),
    (∀ A ∈ L, BK.Increasing A) →
    (percolation d p).real (doList L) ≤ (L.map (fun A => (percolation d p).real A)).prod
  | [], _ => by
    show (percolation d p).real Set.univ ≤ 1
    exact measureReal_le_one
  | [A], _ => by
    show (percolation d p).real A ≤ (percolation d p).real A * 1
    rw [mul_one]
  | A :: B :: L, h => by
    have hrest := doList_probability_le p (B :: L) (fun C hC => h C (List.mem_cons_of_mem _ hC))
    have hinc := doList_increasing (B :: L) (fun C hC => h C (List.mem_cons_of_mem _ hC))
    calc (percolation d p).real (doList (A :: B :: L))
        ≤ (percolation d p).real A * (percolation d p).real (doList (B :: L)) :=
          percolation_bk d p A _ (h A (by simp)) hinc
      _ ≤ (percolation d p).real A *
          ((B :: L).map (fun A => (percolation d p).real A)).prod :=
          mul_le_mul_of_nonneg_left hrest measureReal_nonneg
      _ = _ := by simp

lemma forcesOn_mono {A : Set (Configuration d)} {ω : Configuration d} {F F' : Set (Bond d)}
    (h : ForcesOn A ω F) (hsub : F ⊆ F') : ForcesOn A ω F' :=
  fun θ hθ => h θ (fun e he => hθ e (hsub he))

/-- An increasing event certified inside the `U`-cluster of its root. -/
structure LocalEv (d : ℕ) (U : Finset (Vertex d)) where
  root : Vertex d
  ev : Set (Configuration d)
  inc : BK.Increasing ev
  cert : ∀ ω ∈ ev, ∃ F : Finset (Bond d), ForcesOn ev ω (F : Set (Bond d)) ∧
    ∀ e ∈ F, e.1 ∈ finiteBoxCluster ω U root

variable {U : Finset (Vertex d)}

/-- All events occur, in pairwise disjoint clusters. -/
def distinctLoc (U : Finset (Vertex d)) (L : List (LocalEv d U)) : Set (Configuration d) :=
  {ω | (∀ x ∈ L, ω ∈ x.ev) ∧ L.Pairwise (fun x y =>
    Disjoint (finiteBoxCluster ω U x.root) (finiteBoxCluster ω U y.root))}

lemma distinctLoc_forces : ∀ (L : List (LocalEv d U)) (ω : Configuration d),
    ω ∈ distinctLoc U L →
    ∃ F : Finset (Bond d), ForcesOn (doList (L.map (fun x => x.ev))) ω (F : Set (Bond d)) ∧
      ∀ e ∈ F, ∃ x ∈ L, e.1 ∈ finiteBoxCluster ω U x.root
  | [], ω, _ => ⟨∅, fun _ _ => Set.mem_univ _, fun e he => absurd he (Finset.notMem_empty e)⟩
  | [x], ω, h => by
    obtain ⟨F, hF, hcl⟩ := x.cert ω (h.1 x (by simp))
    exact ⟨F, hF, fun e he => ⟨x, by simp, hcl e he⟩⟩
  | x :: y :: L, ω, h => by
    obtain ⟨hall, hpair⟩ := h
    obtain ⟨hxy, hrestpair⟩ := List.pairwise_cons.mp hpair
    obtain ⟨Fx, hFx, hclx⟩ := x.cert ω (hall x (by simp))
    obtain ⟨Fr, hFr, hclr⟩ := distinctLoc_forces (y :: L) ω
      ⟨fun z hz => hall z (List.mem_cons_of_mem _ hz), hrestpair⟩
    refine ⟨Fx ∪ Fr, ?_, ?_⟩
    · have hdisj : Disjoint (Fx : Set (Bond d)) (Fr : Set (Bond d)) := by
        refine Set.disjoint_left.mpr (fun e hex her => ?_)
        obtain ⟨z, hz, hez⟩ := hclr e her
        exact Finset.disjoint_left.mp (hxy z hz) (hclx e hex) hez
      have h := Section8.forcesOn_disjointOccurrence_union Fx.finite_toSet Fr.finite_toSet
        hdisj hFx hFr
      rw [Finset.coe_union]
      exact h
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact ⟨x, by simp, hclx e he⟩
      · obtain ⟨z, hz, hez⟩ := hclr e he
        exact ⟨z, List.mem_cons_of_mem _ hz, hez⟩

/-- **BK for distinct clusters.** -/
theorem distinct_bk (p : unitInterval) (L : List (LocalEv d U)) :
    (percolation d p).real (distinctLoc U L) ≤
      (L.map (fun x => (percolation d p).real x.ev)).prod := by
  have hsub : distinctLoc U L ⊆ doList (L.map (fun x => x.ev)) := by
    intro ω hω
    obtain ⟨F, hF, _⟩ := distinctLoc_forces L ω hω
    exact hF ω (fun _ _ => rfl)
  have hinc : ∀ A ∈ L.map (fun x => x.ev), BK.Increasing A := by
    intro A hA
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hA
    exact x.inc
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((doList_probability_le p _ hinc).trans_eq ?_)
  rw [List.map_map]
  rfl

/-- Vertices of a restricted walk from `a` lie in the cluster of `a`. -/
lemma walk_support_mem_cluster {ω : Configuration d} {T : Set (Vertex d)}
    (hT : T ⊆ (U : Set (Vertex d))) {a b : Vertex d} (haT : a ∈ T)
    (π : (restrictedGraph ω T).Walk a b) : ∀ z ∈ π.support, z ∈ finiteBoxCluster ω U a := by
  intro z hz
  have hzT := restrictedWalk_support π haT z hz
  refine (mem_finiteBoxCluster ω U a z).mpr ⟨hT hzT, ?_⟩
  exact Reachable.mono (restrictedGraph_mono ω hT) ⟨π.takeUntil z hz⟩

/-- A restricted connection has a certificate inside the cluster of its start. -/
lemma conn_cert_in_cluster {ω : Configuration d} {T : Set (Vertex d)}
    (hT : T ⊆ (U : Set (Vertex d))) {a b : Vertex d}
    (h : ω ∈ connectionToSetEvent T a {b}) :
    ∃ F : Finset (Bond d), ForcesOn (connectionToSetEvent T a {b}) ω (F : Set (Bond d)) ∧
      ∀ e ∈ F, e.1 ∈ finiteBoxCluster ω U a := by
  obtain ⟨haT, y, hy, _, hreach⟩ := h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨π⟩ := hreach
  have hle : restrictedGraph ω T ≤ openGraph ω := fun _ _ h => h.1
  have hsupp : ∀ z ∈ (π.mapLe hle).support, z ∈ T := by
    intro z hz
    rw [Walk.support_mapLe_eq_support] at hz
    exact restrictedWalk_support π haT z hz
  obtain ⟨F, hFo, hFe, hF⟩ := openWalk_certificate (π.mapLe hle) T hsupp
  refine ⟨F, fun θ hθ => hF θ (fun e he => (hθ e he).trans (hFo e he)), fun e he => ?_⟩
  have hmem := (π.mapLe hle).fst_mem_support_of_mem_edges (hFe e he)
  rw [Walk.support_mapLe_eq_support] at hmem
  exact walk_support_mem_cluster hT haT π _ hmem

/-- A restricted connection as a local event. -/
def connLoc (U : Finset (Vertex d)) (T : Set (Vertex d)) (hT : T ⊆ (U : Set (Vertex d)))
    (a b : Vertex d) : LocalEv d U where
  root := a
  ev := connectionToSetEvent T a {b}
  inc := connectionToSetEvent_increasing T a {b}
  cert := fun _ h => conn_cert_in_cluster hT h

/-- Add the requirement that the root is joined to `w` inside `U`. -/
def LocalEv.withTarget (x : LocalEv d U) (w : Vertex d) : LocalEv d U where
  root := x.root
  ev := x.ev ∩ connectionToSetEvent (U : Set (Vertex d)) x.root {w}
  inc := fun _ _ hle h =>
    ⟨x.inc hle h.1, connectionToSetEvent_increasing _ _ _ hle h.2⟩
  cert := fun ω h => by
    obtain ⟨F1, hF1, hc1⟩ := x.cert ω h.1
    obtain ⟨F2, hF2, hc2⟩ := conn_cert_in_cluster (U := U) (le_refl _) h.2
    refine ⟨F1 ∪ F2, fun θ hθ => ⟨hF1 θ (fun e he => hθ e ?_), hF2 θ (fun e he => hθ e ?_)⟩,
      fun e he => ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp he))
    · exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp he))
    · rcases Finset.mem_union.mp he with he | he
      · exact hc1 e he
      · exact hc2 e he

lemma distinctLoc_inter_mem_subset (L₁ L₂ : List (LocalEv d U)) (x : LocalEv d U)
    (hx : x.root ∈ U) (w : Vertex d) :
    distinctLoc U (L₁ ++ x :: L₂) ∩ {ω | w ∈ finiteBoxCluster ω U x.root} ⊆
      distinctLoc U (L₁ ++ x.withTarget w :: L₂) := by
  rintro ω ⟨⟨hall, hpair⟩, hw⟩
  have hwm := (mem_finiteBoxCluster ω U x.root w).mp hw
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases List.mem_append.mp hz with hz | hz
    · exact hall z (List.mem_append_left _ hz)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨hall x (List.mem_append_right _ (by simp)),
          Finset.mem_coe.mpr hx, w, rfl, Finset.mem_coe.mpr hwm.1, hwm.2⟩
      · exact hall z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
  · have hmap : (L₁ ++ x.withTarget w :: L₂).map (fun y => y.root) =
        (L₁ ++ x :: L₂).map (fun y => y.root) := by simp [LocalEv.withTarget]
    have h1 : ((L₁ ++ x :: L₂).map (fun y => y.root)).Pairwise (fun a b =>
        Disjoint (finiteBoxCluster ω U a) (finiteBoxCluster ω U b)) :=
      (List.pairwise_map (f := fun y : LocalEv d U => y.root)
        (R := fun a b => Disjoint (finiteBoxCluster ω U a) (finiteBoxCluster ω U b))).mpr hpair
    rw [← hmap] at h1
    exact (List.pairwise_map (f := fun y : LocalEv d U => y.root)
      (R := fun a b => Disjoint (finiteBoxCluster ω U a) (finiteBoxCluster ω U b))).mp h1

/-- A restricted connection survives changes off the reveal of its start. -/
lemma conn_stable {T : Set (Vertex d)} (hT : T ⊆ (U : Set (Vertex d))) {a b : Vertex d}
    {ω ω' : Configuration d}
    (hagree : ∀ e ∈ clusterRevealBonds U (finiteBoxCluster ω U a), ω' e = ω e)
    (h : ω ∈ connectionToSetEvent T a {b}) : ω' ∈ connectionToSetEvent T a {b} := by
  obtain ⟨haT, y, hy, hbT, hreach⟩ := h
  obtain ⟨π⟩ := hreach
  refine ⟨haT, y, hy, hbT, ?_⟩
  refine reachable_of_walk_good (fun z => z ∈ finiteBoxCluster ω U a) ?_ π
    (walk_support_mem_cluster hT haT π)
  intro e he1 he2 hg1 _ heo
  rw [hagree e ((mem_clusterRevealBonds U _ e).mpr ⟨hT he1, hT he2, Or.inl hg1⟩)]
  exact heo

set_option maxHeartbeats 800000 in
/-- **One step of the distinct-cluster construction.** -/
theorem distinct_step (p : unitInterval) (L : List (LocalEv d U))
    (hroot : ∀ x ∈ L, x.root ∈ U)
    (hstable : ∀ x ∈ L, ∀ ω ω' : Configuration d,
      (∀ e ∈ clusterRevealBonds U (finiteBoxCluster ω U x.root), ω' e = ω e) →
      ω ∈ x.ev → ω' ∈ x.ev)
    (T : Set (Vertex d)) (hT : T ⊆ (U : Set (Vertex d))) (a b : Vertex d) :
    (percolation d p).real (distinctLoc U L) *
        (percolation d p).real (connectionToSetEvent T a {b}) ≤
      (percolation d p).real (distinctLoc U (connLoc U T hT a b :: L)) +
      ∑ w ∈ U, (percolation d p).real
          (distinctLoc U L ∩ {ω | ∃ x ∈ L, w ∈ finiteBoxCluster ω U x.root}) *
        (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent T a {w})
          (connectionToSetEvent T w {b}) ω} := by
  have hR : (L.map (fun x => x.root)).toFinset ⊆ U := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    exact hroot x hx
  have hmemR : ∀ x ∈ L, x.root ∈ (L.map (fun x => x.root)).toFinset :=
    fun x hx => List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hG : ∀ ω ω' : Configuration d,
      (∀ e ∈ revealRoots U (L.map (fun x => x.root)).toFinset ω, ω' e = ω e) →
      ω ∈ distinctLoc U L → ω' ∈ distinctLoc U L := by
    intro ω ω' hagree ⟨hall, hpair⟩
    have hcl : ∀ x ∈ L, finiteBoxCluster ω' U x.root = finiteBoxCluster ω U x.root :=
      fun x hx => cluster_eq_of_agree_reveal U _ hR hagree (hmemR x hx)
    refine ⟨fun x hx => hstable x hx ω ω' (fun e he =>
      hagree e (Finset.mem_biUnion.mpr ⟨x.root, hmemR x hx, he⟩)) (hall x hx), ?_⟩
    exact hpair.imp_of_mem (fun {x y} hx hy h => by rw [hcl x hx, hcl y hy]; exact h)
  have hstep := off_reveal_step p U (L.map (fun x => x.root)).toFinset hR (distinctLoc U L) hG
    T hT a b
  have hfirst : (percolation d p).real (distinctLoc U L ∩ (connectionToSetEvent T a {b} ∩
      {ω | ∀ r ∈ (L.map (fun x => x.root)).toFinset, a ∉ finiteBoxCluster ω U r})) ≤
      (percolation d p).real (distinctLoc U (connLoc U T hT a b :: L)) := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨⟨hall, hpair⟩, hconn, hnot⟩
    have haU : a ∈ U := Finset.mem_coe.mp (hT hconn.1)
    refine ⟨fun x hx => ?_, List.pairwise_cons.mpr ⟨fun y hy => ?_, hpair⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hconn
      · exact hall x hx
    · refine Finset.disjoint_left.mpr (fun z hza hzy => ?_)
      have h1 := (mem_finiteBoxCluster ω U a z).mp hza
      have h2 := (mem_finiteBoxCluster ω U y.root z).mp hzy
      exact hnot y.root (hmemR y hy)
        ((mem_finiteBoxCluster ω U y.root a).mpr ⟨haU, h2.2.trans h1.2.symm⟩)
  have hsecond : ∑ w ∈ U, (percolation d p).real (distinctLoc U L ∩
        {ω | ∃ r ∈ (L.map (fun x => x.root)).toFinset, w ∈ finiteBoxCluster ω U r}) *
        (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent T a {w})
          (connectionToSetEvent T w {b}) ω} ≤
      ∑ w ∈ U, (percolation d p).real
          (distinctLoc U L ∩ {ω | ∃ x ∈ L, w ∈ finiteBoxCluster ω U x.root}) *
        (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent T a {w})
          (connectionToSetEvent T w {b}) ω} := by
    refine Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_right ?_ measureReal_nonneg)
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨hG', r, hr, hwr⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    exact ⟨hG', x, hx, hwr⟩
  linarith

end NearCritical.SplitCrossDirect
end
