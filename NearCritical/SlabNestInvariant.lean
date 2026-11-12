module

public import NearCritical.SlabNestAssembly

/-! The invariant `Q` of the slab nest rule, with its root and join parts.

`slabQ … q v ℓ`: the nest `ℓ` of the cube `v` under the sample `q` consists of
`k` typical clusters of the first-copy cube configuration, carries that cube's
heart union, and every point of every cluster of the nest is joined to `F`
inside `S` in the resampled configuration `rsCfg`.

* `slabQ_root`: the root nest satisfies it with `F` the root cube (reflexive
  reachability).
* `slabQ_join`: it implies `slabNestJoined` (a cluster of the nest is non-empty
  and lies in the cube).

The propagation `edgeQ` through a tube step is NOT here.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open scoped Classical
open Section10

variable {d : ℕ}

/-- The invariant of the slab nest rule. -/
def slabQ (d n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters) (k : ℕ)
    (S : Set (Vertex d)) (F : Finset (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (v : centeredBox 2 R)
    (ℓ : SlabNest d) : Prop :=
  ℓ.1.card = k ∧
  ℓ.1 ⊆ typicalClusterFamily typ n (coarseShift (d := d) n v.1)
    (slabCubeConfig d n A R (rsΦ d n A R q) v) ∧
  ℓ.2 = heartClusterUnion (slabCubeConfig d n A R (rsΦ d n A R q) v)
    (typicalCube n (coarseShift (d := d) n v.1))
    (typicalHeart n (coarseShift (d := d) n v.1) typ.heartRatio) ∧
  ∀ C ∈ ℓ.1, ∀ x ∈ C, ∃ a ∈ F,
    (restrictedGraph (rsCfg d n R typ.heartRatio (slabKfix n A R) q) S).Reachable a x

/-- A typical cluster lies in its cube and is non-empty. -/
lemma typicalCluster_subset_nonempty (hd : 0 < d) (a : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω : Configuration d) (C : Finset (Vertex d))
    (hC : C ∈ typicalClusterFamily a t z ω) : C ⊆ typicalCube t z ∧ C.Nonempty := by
  obtain ⟨_, hT⟩ := (mem_typicalClusterFamily a t z ω C).mp hC
  refine ⟨hT.1.trans (heartClusterUnion_subset ω _ _), ?_⟩
  obtain ⟨y, hy⟩ := hT.2.1 ((⟨0, hd⟩ : Fin d), true)
  exact ⟨y, (Finset.mem_inter.mp hy).1⟩

theorem slabQ_root (n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters) (k : ℕ)
    (hd : 0 < d) (S : Set (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (ℓ : SlabNest d)
    (h : slabRootNest d n A R typ k (rsΦ d n A R q) = some ℓ) :
    slabQ d n A R typ k S (typicalCube n (coarseShift (d := d) n (0 : Vertex 2))) q
      ⟨0, zero_mem_centeredBox_two R⟩ ℓ := by
  unfold slabRootNest rootNestOf at h
  split_ifs at h with hc
  have hℓ := Option.some.inj h
  have hspec := Classical.choose_spec (Finset.exists_subset_card_eq hc.2)
  subst hℓ
  refine ⟨hspec.2, hspec.1, rfl, ?_⟩
  intro C hC x hx
  have hsub := (typicalCluster_subset_nonempty hd typ n _ _ C (hspec.1 hC)).1
  exact ⟨x, hsub hx, SimpleGraph.Reachable.refl x⟩

theorem slabQ_join {n : ℕ} (hn : 0 < n) (hd : 0 < d) (A : Finset (Bond d)) (R : ℕ)
    (typ : TypicalParameters) {k : ℕ} (hk : 0 < k) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (v : centeredBox 2 R) (ℓ : SlabNest d) (h : slabQ d n A R typ k S F q v ℓ) :
    slabNestJoined n S F (rsCfg d n R typ.heartRatio (slabKfix n A R) q) (v : Vertex 2) := by
  obtain ⟨hcard, hfam, -, hreach⟩ := h
  have hne : ℓ.1.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨C, hC⟩ := hne
  obtain ⟨hsub, ⟨x, hx⟩⟩ := typicalCluster_subset_nonempty hd typ n _ _ C (hfam hC)
  obtain ⟨a, ha, hr⟩ := hreach C hC x hx
  exact ⟨a, ha, x, (mem_typicalCube_coarseShift hn v.1 x).mp (hsub hx), hr⟩

end NearCritical
