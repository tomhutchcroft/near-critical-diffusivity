module

public import NearCritical.Section10RouteEdges
public import Mathlib.Data.Sym.Sym2

/-! Common unordered route edges. Charging uses the first route's directed
representatives, permitting opposite orientations between the two routes.
Nearest-neighbour physical tube identification and the route law remain open. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
variable {A : Type*}

/-- Both endpoints of a computed route edge are actual route sites. -/
theorem routeEdge_head_mem {M : ℕ} {X : ℕ → A} {z w : ℕ × A}
    (he : (z,w) ∈ routeEdges M X) : w ∈ routeSites M X := by
  obtain ⟨hz,hn⟩ := (mem_routeEdges M X z w).mp he
  have hj : z.1 < M := ((mem_routeSites M X z.1 z.2).mp hz).1
  unfold routeNext at hn
  split_ifs at hn with hslot hlevel hprev
  · have hw : (z.1+1,X z.1) = w := Option.some.inj hn
    rw [← hw]
    apply (mem_routeSites M X (z.1+1) (X z.1)).mpr
    exact ⟨hlevel,Or.inr (by simp)⟩
  · have hw : (z.1,X z.1) = w := Option.some.inj hn
    rw [← hw]
    exact (mem_routeSites M X z.1 (X z.1)).mpr ⟨hj,Or.inl rfl⟩

def routeUnorderedEdges (M : ℕ) (X : ℕ → A) : Finset (Sym2 (ℕ × A)) :=
  (routeEdges M X).image fun e => s(e.1,e.2)

/-- If an unordered edge occurs in a route, either endpoint is a route site. -/
theorem unordered_route_edge_tail_mem {M : ℕ} {X : ℕ → A} {z w : ℕ × A}
    (he : s(z,w) ∈ routeUnorderedEdges M X) : z ∈ routeSites M X := by
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp he
  rcases Sym2.eq_iff.mp heq with ⟨hz,hw⟩ | ⟨hz,hw⟩
  · rw [← hz]
    exact ((mem_routeEdges M X e.1 e.2).mp he).1
  · rw [← hw]
    exact routeEdge_head_mem he

/-- No orientation assumption between routes is needed for the edge budget. -/
theorem common_unordered_route_edges_card_le_common_sites (M : ℕ) (X Y : ℕ → A) :
    ((routeUnorderedEdges M X) ∩ (routeUnorderedEdges M Y)).card ≤
      ((routeSites M X) ∩ (routeSites M Y)).card := by
  let E := (routeEdges M X).filter fun e => s(e.1,e.2) ∈ routeUnorderedEdges M Y
  have hcover : (routeUnorderedEdges M X) ∩ (routeUnorderedEdges M Y) ⊆
      E.image (fun e => s(e.1,e.2)) := by
    intro b hb
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hb
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hy⟩,rfl⟩
  have hinj : Set.InjOn Prod.fst (E : Set ((ℕ × A) × (ℕ × A))) := by
    intro e he f hf ht
    exact routeEdges_tail_injective M X
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 ht
  have hsub : E.image Prod.fst ⊆ (routeSites M X) ∩ (routeSites M Y) := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_filter.mp he
    exact Finset.mem_inter.mpr
      ⟨((mem_routeEdges M X e.1 e.2).mp hx).1,unordered_route_edge_tail_mem hy⟩
  calc
    _ ≤ (E.image (fun e => s(e.1,e.2))).card := Finset.card_le_card hcover
    _ ≤ E.card := Finset.card_image_le
    _ = (E.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Literal unordered common-edge budget in terms of computed common levels. -/
theorem common_unordered_route_edges_card_le_two_levels (M : ℕ) (X Y : ℕ → A) :
    ((routeUnorderedEdges M X) ∩ (routeUnorderedEdges M Y)).card ≤
      2*(commonRouteLevels M X Y).card :=
  (common_unordered_route_edges_card_le_common_sites M X Y).trans
    (common_route_sites_card_le_two_levels M X Y)

end NearCritical.Section10
