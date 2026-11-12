module

public import NearCritical.SlabNestInvariant

/-! First-copy cube-block correspondence, and nest clusters in `rsCfg`.

(i) `slabCubeConfig_agree`: the configuration read from the first-copy block of a
cube agrees with the critical layer of the first sample on the cube's internal
bonds (ambient bonds containing the cube). Hence the typical family, the heart
union and the pre-good status computed from the block are those of the critical
layer of the first sample (`slabCubeConfig_typicalFamily`,
`slabCubeConfig_heartUnion`, `slabCubeConfig_isPreGood`).

(ii) `heartUnion_path_rsCfg`: an open path of the first-sample critical layer
inside a cube that starts in the cube's heart union is an open path of the
resampled configuration `rsCfg` (its bonds are revealed, so `rsCfg` reads the
first copy there). `typicalCluster_connected_rsCfg`: any two points of a typical
cluster of the cube are joined in `rsCfg` inside any `S` containing the cube.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open scoped Classical
open Section10

variable {d : ℕ}

theorem slabCubeConfig_agree {n : ℕ} (hn : 0 < n) (A : Finset (Bond d)) (R : ℕ)
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (v : centeredBox 2 R)
    (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) :
    ∀ e ∈ internalBondSet (typicalCube n (coarseShift (d := d) n v.1)),
      slabCubeConfig d n A R (rsΦ d n A R q) v e = criticalLayer q.1 e := by
  intro e he
  have hin := (internalBond_iff_bondIn hn v.1 e).mp he
  have hmem : ((e, true) : Bond d × Bool) ∈
      slabSprinkleBlocks (d := d) n A (centeredBox 2 R) (Sum.inl v) := by
    simp only [slabSprinkleBlocks, Finset.mem_product, Finset.mem_filter,
      Finset.mem_singleton, and_true]
    exact ⟨hA e hin, hin⟩
  unfold slabCubeConfig blockConfig
  rw [dif_pos hmem]
  rfl

theorem slabCubeConfig_typicalFamily {n : ℕ} (hn : 0 < n) (A : Finset (Bond d)) (R : ℕ)
    (typ : TypicalParameters) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (v : centeredBox 2 R) (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) :
    typicalClusterFamily typ n (coarseShift (d := d) n v.1)
        (slabCubeConfig d n A R (rsΦ d n A R q) v) =
      typicalClusterFamily typ n (coarseShift (d := d) n v.1) (criticalLayer q.1) :=
  typicalClusterFamily_eq_of_internal_agree typ n _ _ _ (slabCubeConfig_agree hn A R q v hA)

theorem slabCubeConfig_heartUnion {n : ℕ} (hn : 0 < n) (A : Finset (Bond d)) (R : ℕ)
    (cc : ℝ) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (v : centeredBox 2 R) (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) :
    heartClusterUnion (slabCubeConfig d n A R (rsΦ d n A R q) v)
        (typicalCube n (coarseShift (d := d) n v.1))
        (typicalHeart n (coarseShift (d := d) n v.1) cc) =
      heartClusterUnion (criticalLayer q.1) (typicalCube n (coarseShift (d := d) n v.1))
        (typicalHeart n (coarseShift (d := d) n v.1) cc) :=
  heartClusterUnion_eq_of_internal_agree _ _ _ (fun _ hx => hx) _ _
    (slabCubeConfig_agree hn A R q v hA)

theorem slabCubeConfig_isPreGood {n : ℕ} (hn : 0 < n) (A : Finset (Bond d)) (R : ℕ)
    (typ : TypicalParameters) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (v : centeredBox 2 R) (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) :
    IsPreGoodCube typ n (coarseShift (d := d) n v.1)
        (slabCubeConfig d n A R (rsΦ d n A R q) v) ↔
      IsPreGoodCube typ n (coarseShift (d := d) n v.1) (criticalLayer q.1) :=
  isPreGoodCube_iff_of_internal_agree typ n _ _ _ (slabCubeConfig_agree hn A R q v hA)

/-- The heart union is closed under restricted adjacency. -/
lemma heartClusterUnion_adj_closed (ω : Configuration d) (Q H : Finset (Vertex d))
    {a c : Vertex d} (ha : a ∈ heartClusterUnion ω Q H)
    (hadj : (restrictedGraph ω (Q : Set (Vertex d))).Adj a c) :
    c ∈ heartClusterUnion ω Q H := by
  unfold heartClusterUnion at ha ⊢
  obtain ⟨h, hh, hah⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨_, hr⟩ := (mem_finiteBoxCluster ω Q h a).mp hah
  exact Finset.mem_biUnion.mpr ⟨h, hh, (mem_finiteBoxCluster ω Q h c).mpr
    ⟨Finset.mem_coe.mp hadj.2.2, hr.trans hadj.reachable⟩⟩

/-- Paths of the first-sample critical layer inside a cube, started in the heart
union, are paths of `rsCfg`. -/
theorem heartUnion_path_rsCfg (n R : ℕ) (cc : ℝ) (Kfix : Finset (Bond d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (v : Vertex 2)
    (hv : v ∈ centeredBox 2 R) (S : Set (Vertex d))
    (hS : (typicalCube n (coarseShift (d := d) n v) : Set (Vertex d)) ⊆ S) :
    ∀ {a b : Vertex d}
      (_w : (restrictedGraph (criticalLayer q.1)
        (typicalCube n (coarseShift (d := d) n v) : Set (Vertex d))).Walk a b),
      a ∈ heartClusterUnion (criticalLayer q.1) (typicalCube n (coarseShift (d := d) n v))
        (typicalHeart n (coarseShift (d := d) n v) cc) →
      (restrictedGraph (rsCfg d n R cc Kfix q) S).Reachable a b := by
  intro a b w
  induction w with
  | nil => intro _; exact SimpleGraph.Reachable.refl _
  | @cons a c b hadj w ih =>
    intro ha
    have hc := heartClusterUnion_adj_closed _ _ _ ha hadj
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) (ih hc)
    obtain ⟨⟨e, he, hends⟩, haQ, hcQ⟩ := hadj
    have haQ' := Finset.mem_coe.mp haQ
    have hcQ' := Finset.mem_coe.mp hcQ
    have hrev : e ∈ unionReveal (centeredBox 2 R)
        (fun v => typicalCube n (coarseShift (d := d) n v))
        (fun v => typicalHeart n (coarseShift (d := d) n v) cc) Kfix (criticalLayer q.1) := by
      unfold unionReveal
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩)
      unfold heartRevealSet
      rw [mem_clusterRevealBonds]
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ haQ', h2 ▸ hcQ', Or.inl (h1 ▸ ha)⟩
      · exact ⟨h1 ▸ hcQ', h2 ▸ haQ', Or.inr (h2 ▸ ha)⟩
    have hagree := resampleLayers_agree (centeredBox 2 R)
      (fun v => typicalCube n (coarseShift (d := d) n v))
      (fun v => typicalHeart n (coarseShift (d := d) n v) cc) Kfix q e hrev
    have hopen : rsCfg d n R cc Kfix q e = true := by
      unfold rsCfg
      refine sprinkleConfiguration_base _ e ?_
      have : criticalLayer (resampleLayers (centeredBox 2 R)
          (fun v => typicalCube n (coarseShift (d := d) n v))
          (fun v => typicalHeart n (coarseShift (d := d) n v) cc) Kfix q) e = true := by
        rw [hagree]
        exact he
      exact this
    exact ⟨⟨e, hopen, hends⟩, hS haQ, hS hcQ⟩

/-- Two points of a typical cluster of a cube are joined in `rsCfg`. -/
theorem typicalCluster_connected_rsCfg (n R : ℕ) (typ : TypicalParameters)
    (Kfix : Finset (Bond d)) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (v : Vertex 2) (hv : v ∈ centeredBox 2 R) (S : Set (Vertex d))
    (hS : (typicalCube n (coarseShift (d := d) n v) : Set (Vertex d)) ⊆ S)
    (C : Finset (Vertex d))
    (hC : C ∈ typicalClusterFamily typ n (coarseShift (d := d) n v) (criticalLayer q.1))
    {x y : Vertex d} (hx : x ∈ C) (hy : y ∈ C) :
    (restrictedGraph (rsCfg d n R typ.heartRatio Kfix q) S).Reachable x y := by
  obtain ⟨hfam, hT⟩ := (mem_typicalClusterFamily typ n _ _ C).mp hC
  obtain ⟨r, _, hr⟩ := (mem_finiteClusterFamily _ _ C).mp hfam
  subst hr
  obtain ⟨_, hrx⟩ := (mem_finiteBoxCluster _ _ r x).mp hx
  obtain ⟨_, hry⟩ := (mem_finiteBoxCluster _ _ r y).mp hy
  obtain ⟨w⟩ := hrx.symm.trans hry
  exact heartUnion_path_rsCfg n R typ.heartRatio Kfix q v hv S hS w (hT.1 hx)

end NearCritical
