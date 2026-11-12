module

public import NearCritical.SplitCrossDirectSkeleton
public import NearCritical.ClusterRevealSupport
public import NearCritical.ResamplingInfinite
public import NearCritical.ThreePointTreeGraphDerivation

/-! The off-cluster step (item D of the direct proof of `SplitCrossInput`).

Work in a finite vertex domain `U` (the outside domain). For a finite set `R`
of roots, `revealRoots U R ω` is the set of bonds of `U` touching the
`U`-cluster of some root: a stopping set.

`off_reveal_step`: let `G` be an event determined by the reveal (if `ω'` agrees
with `ω` on `revealRoots U R ω` and `ω ∈ G` then `ω' ∈ G`), and let
`T ⊆ U`. Then

  `P[G] · P[a ↔ b in T] ≤ P[G, a ↔ b in T, a in none of the root clusters]`
  `      + Σ_{w ∈ U} P[G, w in a root cluster] · P[{a ↔ w in T} ∘ {w ↔ b in T}]`.

Proof: resample every bond of `U` outside the reveal with an independent
configuration `ω'` (`resample_infinite_law`). If the `ω'`-path from `a` to `b`
avoids the revealed clusters it survives in the composite, whose reveal and
root clusters are those of `ω`; otherwise it meets a revealed cluster at some
`w`, and its two halves are edge-disjoint. The error term is a union of
RECTANGLES, so no conditional probability appears.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators ENNReal

variable {d : ℕ}

/-- Bonds of `U` touching the `U`-cluster of a root in `R`. -/
def revealRoots (U R : Finset (Vertex d)) (ω : Configuration d) : Finset (Bond d) :=
  R.biUnion fun r => clusterRevealBonds U (finiteBoxCluster ω U r)

lemma revealRoots_subset (U R : Finset (Vertex d)) (ω : Configuration d) :
    revealRoots U R ω ⊆ internalBondSet U := by
  intro e he
  obtain ⟨r, _, her⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_filter.mp her).1

lemma cluster_eq_of_agree_reveal (U R : Finset (Vertex d)) (hR : R ⊆ U)
    {ω ω' : Configuration d} (h : ∀ e ∈ revealRoots U R ω, ω' e = ω e) {r : Vertex d}
    (hr : r ∈ R) : finiteBoxCluster ω' U r = finiteBoxCluster ω U r :=
  finiteBoxCluster_eq_of_reveal_agree U _ r (hR hr) rfl
    (fun e he => (h e (Finset.mem_biUnion.mpr ⟨r, hr, he⟩)).symm)

lemma revealRoots_stopping (U R : Finset (Vertex d)) (hR : R ⊆ U) (ω ω' : Configuration d)
    (h : ∀ e ∈ revealRoots U R ω, ω' e = ω e) : revealRoots U R ω' = revealRoots U R ω := by
  unfold revealRoots
  exact Finset.biUnion_congr rfl (fun r hr => by rw [cluster_eq_of_agree_reveal U R hR h hr])

/-- A walk whose vertices are all `Good` survives in any configuration that
keeps its open bonds between `Good` vertices of `T`. -/
lemma reachable_of_walk_good {ω' θ : Configuration d} {T : Set (Vertex d)}
    (Good : Vertex d → Prop)
    (hopen : ∀ e : Bond d, e.1 ∈ T → bondTip e ∈ T → Good e.1 → Good (bondTip e) →
      ω' e = true → θ e = true) :
    ∀ {x y : Vertex d} (π : (restrictedGraph ω' T).Walk x y), (∀ z ∈ π.support, Good z) →
      (restrictedGraph θ T).Reachable x y := by
  intro x y π
  induction π with
  | nil => exact fun _ => Reachable.refl _
  | @cons x z y hxz π ih =>
    intro hgood
    have hgx : Good x := hgood x (by simp)
    have hgz : Good z := hgood z (by simp)
    have hrest := ih (fun t ht => hgood t (by simp [ht]))
    obtain ⟨⟨e, he, hends⟩, hxT, hzT⟩ := hxz
    have hadj : (restrictedGraph θ T).Adj x z := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨⟨e, hopen e (h1 ▸ hxT) (h2 ▸ hzT) (h1 ▸ hgx) (h2 ▸ hgz) he, Or.inl ⟨h1, h2⟩⟩,
          hxT, hzT⟩
      · refine ⟨⟨e, hopen e (h1 ▸ hzT) (h2 ▸ hxT) (h1 ▸ hgz) (h2 ▸ hgx) he, Or.inr ⟨h1, h2⟩⟩,
          hxT, hzT⟩
    exact hadj.reachable.trans hrest

/-- A path through `w` gives the disjoint occurrence of its two halves. -/
lemma disjointOccurrence_of_path_through {ω' : Configuration d} {T : Set (Vertex d)}
    {a b w : Vertex d} (haT : a ∈ T) (π : (restrictedGraph ω' T).Walk a b) (hπ : π.IsPath)
    (hw : w ∈ π.support) :
    DisjointOccurrence (connectionToSetEvent T a {w}) (connectionToSetEvent T w {b}) ω' := by
  have hle : restrictedGraph ω' T ≤ openGraph ω' := fun _ _ h => h.1
  have hsupp := restrictedWalk_support π haT
  have hwT : w ∈ T := hsupp w hw
  have h1supp : ∀ z ∈ ((π.takeUntil w hw).mapLe hle).support, z ∈ T := by
    intro z hz
    rw [Walk.support_mapLe_eq_support] at hz
    exact hsupp z (π.support_takeUntil_subset_support hw hz)
  have h2supp : ∀ z ∈ ((π.dropUntil w hw).mapLe hle).support, z ∈ T := by
    intro z hz
    rw [Walk.support_mapLe_eq_support] at hz
    exact restrictedWalk_support (π.dropUntil w hw) hwT z hz
  obtain ⟨F1, hF1o, hF1e, hF1⟩ := openWalk_certificate ((π.takeUntil w hw).mapLe hle) T h1supp
  obtain ⟨F2, hF2o, hF2e, hF2⟩ := openWalk_certificate ((π.dropUntil w hw).mapLe hle) T h2supp
  refine ⟨(F1 : Set (Bond d)), (F2 : Set (Bond d)), F1.finite_toSet, F2.finite_toSet, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.mpr (fun e he1 he2 => ?_)
    have h1 := hF1e e he1
    have h2 := hF2e e he2
    rw [Walk.edges_mapLe_eq_edges] at h1 h2
    have hnd := hπ.isTrail.edges_nodup
    rw [← π.take_spec hw, Walk.edges_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ h1 _ h2 rfl
  · intro η hη
    exact hF1 η (fun e he => (hη e he).trans (hF1o e he))
  · intro η hη
    exact hF2 η (fun e he => (hη e he).trans (hF2o e he))

set_option maxHeartbeats 800000 in
/-- **Off-cluster step.** -/
theorem off_reveal_step (p : unitInterval) (U R : Finset (Vertex d)) (hR : R ⊆ U)
    (G : Set (Configuration d))
    (hG : ∀ ω ω' : Configuration d, (∀ e ∈ revealRoots U R ω, ω' e = ω e) → ω ∈ G → ω' ∈ G)
    (T : Set (Vertex d)) (hT : T ⊆ (U : Set (Vertex d))) (a b : Vertex d) :
    (percolation d p).real G * (percolation d p).real (connectionToSetEvent T a {b}) ≤
      (percolation d p).real (G ∩ (connectionToSetEvent T a {b} ∩
        {ω | ∀ r ∈ R, a ∉ finiteBoxCluster ω U r})) +
      ∑ w ∈ U, (percolation d p).real (G ∩ {ω | ∃ r ∈ R, w ∈ finiteBoxCluster ω U r}) *
        (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent T a {w})
          (connectionToSetEvent T w {b}) ω} := by
  obtain ⟨hφm, hφ⟩ := resample_infinite_law (fun _ : Bond d => bernoulliMeasure true false p)
    (internalBondSet U) (revealRoots U R) (revealRoots_subset U R)
    (revealRoots_stopping U R hR)
  have hφ' : Measure.map (resampleOn (internalBondSet U) (revealRoots U R))
      ((percolation d p).prod (percolation d p)) = percolation d p := hφ
  -- the containment
  have hsub : G ×ˢ connectionToSetEvent T a {b} ⊆
      (resampleOn (internalBondSet U) (revealRoots U R)) ⁻¹'
        (G ∩ (connectionToSetEvent T a {b} ∩ {ω | ∀ r ∈ R, a ∉ finiteBoxCluster ω U r})) ∪
      ⋃ w ∈ U, ((G ∩ {ω | ∃ r ∈ R, w ∈ finiteBoxCluster ω U r}) ×ˢ
        {ω | DisjointOccurrence (connectionToSetEvent T a {w})
          (connectionToSetEvent T w {b}) ω}) := by
    rintro ⟨ω, ω'⟩ ⟨hω, hω'⟩
    have hωG : ω ∈ G := hω
    obtain ⟨haT, y, hy, hbT, hreach⟩ := hω'
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨π, hπ⟩ := hreach.exists_isPath
    by_cases hhit : ∃ w ∈ π.support, ∃ r ∈ R, w ∈ finiteBoxCluster ω U r
    · obtain ⟨w, hw, r, hr, hwr⟩ := hhit
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨w, finiteBoxCluster_subset ω U r hwr, ?_⟩)
      exact ⟨⟨hωG, r, hr, hwr⟩, disjointOccurrence_of_path_through haT π hπ hw⟩
    · left
      have hgood : ∀ z ∈ π.support, ∀ r ∈ R, z ∉ finiteBoxCluster ω U r :=
        fun z hz r hr hzr => hhit ⟨z, hz, r, hr, hzr⟩
      have hagree : ∀ e ∈ revealRoots U R ω,
          resampleOn (internalBondSet U) (revealRoots U R) (ω, ω') e = ω e := by
        intro e he
        unfold resampleOn
        rw [if_neg (fun h => h.2 he)]
      have hcl : ∀ r ∈ R, finiteBoxCluster
          (resampleOn (internalBondSet U) (revealRoots U R) (ω, ω')) U r =
          finiteBoxCluster ω U r := fun r hr => cluster_eq_of_agree_reveal U R hR hagree hr
      refine ⟨hG ω _ hagree hωG, ⟨haT, y, rfl, hbT, ?_⟩, ?_⟩
      · refine reachable_of_walk_good (fun z => ∀ r ∈ R, z ∉ finiteBoxCluster ω U r) ?_ π hgood
        intro e he1 he2 hg1 hg2 heo
        show resampleOn (internalBondSet U) (revealRoots U R) (ω, ω') e = true
        have hnot : e ∉ revealRoots U R ω := by
          intro hmem
          obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp hmem
          rcases ((mem_clusterRevealBonds U _ e).mp her).2.2 with h | h
          · exact hg1 r hr h
          · exact hg2 r hr h
        unfold resampleOn
        rw [if_pos ⟨(mem_internalBondSet U e).mpr ⟨hT he1, hT he2⟩, hnot⟩]
        exact heo
      · intro r hr
        rw [hcl r hr]
        exact hgood a π.start_mem_support r hr
  -- measures
  have hENN : percolation d p G * percolation d p (connectionToSetEvent T a {b}) ≤
      percolation d p (G ∩ (connectionToSetEvent T a {b} ∩
        {ω | ∀ r ∈ R, a ∉ finiteBoxCluster ω U r})) +
      ∑ w ∈ U, percolation d p (G ∩ {ω | ∃ r ∈ R, w ∈ finiteBoxCluster ω U r}) *
        percolation d p {ω | DisjointOccurrence (connectionToSetEvent T a {w})
          (connectionToSetEvent T w {b}) ω} := by
    calc percolation d p G * percolation d p (connectionToSetEvent T a {b})
        = ((percolation d p).prod (percolation d p))
            (G ×ˢ connectionToSetEvent T a {b}) := (Measure.prod_prod _ _).symm
      _ ≤ _ := (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ _ := by
          refine add_le_add ?_ ?_
          · exact (Measure.le_map_apply hφm.aemeasurable _).trans_eq (by rw [hφ'])
          · refine (measure_biUnion_finset_le U _).trans (Finset.sum_le_sum (fun w _ => ?_))
            exact (Measure.prod_prod _ _).le
  have hfin : ∀ w, percolation d p (G ∩ {ω | ∃ r ∈ R, w ∈ finiteBoxCluster ω U r}) *
      percolation d p {ω | DisjointOccurrence (connectionToSetEvent T a {w})
        (connectionToSetEvent T w {b}) ω} ≠ ⊤ :=
    fun w => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hsumfin : (∑ w ∈ U, percolation d p (G ∩ {ω | ∃ r ∈ R, w ∈ finiteBoxCluster ω U r}) *
      percolation d p {ω | DisjointOccurrence (connectionToSetEvent T a {w})
        (connectionToSetEvent T w {b}) ω}) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun w _ => hfin w)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, hsumfin⟩) hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (measure_ne_top _ _) hsumfin,
    ENNReal.toReal_sum (fun w _ => hfin w)] at hreal
  simp_rw [ENNReal.toReal_mul] at hreal
  exact hreal

end NearCritical.SplitCrossDirect
end
