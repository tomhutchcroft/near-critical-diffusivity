module
public import NearCritical.NestRepresentative
public import NearCritical.Section9SprinklingConnection

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- If a union of (k) source boundaries reaches at least (k^2) target
indices, one source boundary reaches at least (k) of those indices. -/
theorem slab_exists_source_with_connected_offspring {d : ℕ} {ι κ : Type*}
    (ω : Configuration d) (D : Set (Vertex d))
    (nest : Finset ι) (sources : ι → Finset (Vertex d))
    (I : Finset κ) (targets : κ → Finset (Vertex d))
    {k : ℕ} (hk : 0 < k) (hcard : nest.card = k)
    (hcount : k * k ≤
      (I.filter fun j => ∃ x ∈ nest.biUnion sources,
        ω ∈ connectionToSetEvent D x (targets j : Set (Vertex d))).card) :
    ∃ c ∈ nest, k ≤ (I.filter fun j => ∃ x ∈ sources c,
        ω ∈ connectionToSetEvent D x (targets j : Set (Vertex d))).card := by
  let offspring := fun c => I.filter fun j => ∃ x ∈ sources c,
    ω ∈ connectionToSetEvent D x (targets j : Set (Vertex d))
  have hsub : (I.filter fun j => ∃ x ∈ nest.biUnion sources,
      ω ∈ connectionToSetEvent D x (targets j : Set (Vertex d))) ⊆
      nest.biUnion offspring := by
    intro j hj
    obtain ⟨hjI,x,hx,hconn⟩ := Finset.mem_filter.mp hj
    obtain ⟨c,hc,hxc⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hjI,x,hxc,hconn⟩⟩
  exact nest_exists_large_offspring nest offspring hk hcard
    (hcount.trans (Finset.card_le_card hsub))

end NearCritical
