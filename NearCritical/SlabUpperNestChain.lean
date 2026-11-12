module

public import NearCritical.SlabUpperThreshold

/-! Deterministic pigeonhole core of source prop.slab.upper (source 6097–6100):
the explored `k`-nests occupy pairwise disjoint vertex sets (distinct cubes), and
each is joined by open paths to one of the finitely many clusters of the root
nest. Infinitely many explored nests therefore force one of those finitely many
root clusters to be infinite, which lies in the slab. No probability here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- An infinite family of pairwise disjoint nonempty sets, all reachable from a
finite root set, forces some root to have an infinite cluster. -/
theorem exists_root_infinite_of_disjoint_reachable {V ι : Type*} (G : SimpleGraph V)
    {T : Set ι} (hT : T.Infinite) (A : ι → Set V) (hne : ∀ t ∈ T, (A t).Nonempty)
    (hdisj : T.PairwiseDisjoint A) (R : Finset V)
    (hcover : ∀ t ∈ T, ∀ a ∈ A t, ∃ r ∈ R, G.Reachable r a) :
    ∃ r ∈ R, {y | G.Reachable r y}.Infinite := by
  by_contra hfin
  have hfin' : ∀ r ∈ (R : Set V), {y | G.Reachable r y}.Finite := fun r hr ↦
    Set.not_infinite.mp (fun hinf ↦ hfin ⟨r, hr, hinf⟩)
  have hU : (⋃ r ∈ (R : Set V), {y | G.Reachable r y}).Finite :=
    R.finite_toSet.biUnion hfin'
  have hne' : ∀ t ∈ T, ∃ x, x ∈ A t := hne
  obtain ⟨t₀, ht₀⟩ := hT.nonempty
  obtain ⟨x₀, -⟩ := hne' t₀ ht₀
  haveI : Nonempty V := ⟨x₀⟩
  choose! a ha using hne'
  have hinj : Set.InjOn a T := by
    intro s hs t ht hst
    by_contra hst'
    have hd : Disjoint (A s) (A t) := hdisj hs ht hst'
    have hat : a s ∈ A t := by
      rw [hst]
      exact ha t ht
    exact Set.disjoint_left.mp hd (ha s hs) hat
  have himg : (a '' T).Infinite := Set.Infinite.image hinj hT
  apply himg
  apply hU.subset
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, hr, hreach⟩ := hcover t ht (a t) (ha t ht)
  exact Set.mem_biUnion (Finset.mem_coe.mpr hr) hreach

/-- Slab form: disjoint explored nests in `S`, each joined inside `S` to one of
finitely many roots, put the configuration in the event that some vertex has an
infinite `S`-restricted cluster. -/
theorem mem_restrictedSomeInfiniteEvent_of_nest_chain {d : ℕ} {ι : Type*}
    (S : Set (Vertex d)) (ω : Configuration d) {T : Set ι} (hT : T.Infinite)
    (A : ι → Set (Vertex d)) (hne : ∀ t ∈ T, (A t).Nonempty)
    (hdisj : T.PairwiseDisjoint A) (R : Finset (Vertex d))
    (hcover : ∀ t ∈ T, ∀ a ∈ A t, ∃ r ∈ R, (restrictedGraph ω S).Reachable r a) :
    ω ∈ restrictedSomeInfiniteEvent S := by
  obtain ⟨r, -, hr⟩ :=
    exists_root_infinite_of_disjoint_reachable (restrictedGraph ω S) hT A hne hdisj R hcover
  exact ⟨r, hr⟩

end NearCritical
