module

public import NearCritical.Section10RouteSites

/-! The directed edge set of the Section10 route, with repeated horizontal
sites omitted. Its outgoing edge is a function of the site. Consequently common
edges inject into common sites, proving the deterministic edge count in EIT.
The random route law and the exponential tail are separate obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
variable {A : Type*}

def routeNext (M : ℕ) (X : ℕ → A) (z : ℕ × A) : Option (ℕ × A) :=
  if z.2 = X z.1 then
    if z.1 + 1 < M then some (z.1+1, X z.1) else none
  else if z.2 = X (z.1-1) then some (z.1, X z.1) else none

def routeEdges (M : ℕ) (X : ℕ → A) : Finset ((ℕ × A) × (ℕ × A)) :=
  (routeSites M X).biUnion fun z =>
    match routeNext M X z with
    | none => ∅
    | some w => {(z,w)}

/-- Edge membership records its actual source site and computed next site. -/
theorem mem_routeEdges (M : ℕ) (X : ℕ → A) (z w : ℕ × A) :
    (z,w) ∈ routeEdges M X ↔ z ∈ routeSites M X ∧ routeNext M X z = some w := by
  simp only [routeEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨v,hv,he⟩
    cases hn : routeNext M X v with
    | none => simp [hn] at he
    | some v' =>
      have heq : (z,w) = (v,v') := by simpa only [hn,Finset.mem_singleton] using he
      cases heq
      exact ⟨hv,hn⟩
  · rintro ⟨hz,hn⟩
    exact ⟨z,hz,by simp [hn]⟩

/-- A route uses at most one outgoing edge at each site, including stays. -/
theorem routeEdges_tail_injective (M : ℕ) (X : ℕ → A) :
    Set.InjOn Prod.fst (routeEdges M X : Set ((ℕ × A) × (ℕ × A))) := by
  intro e he f hf htail
  obtain ⟨heS,heN⟩ := (mem_routeEdges M X e.1 e.2).mp he
  obtain ⟨hfS,hfN⟩ := (mem_routeEdges M X f.1 f.2).mp hf
  rw [htail] at heN
  have hhead : e.2 = f.2 := Option.some.inj (heN.symm.trans hfN)
  exact Prod.ext htail hhead

/-- Common directed edges inject into the literal common site set. -/
theorem common_route_edges_card_le_common_sites (M : ℕ) (X Y : ℕ → A) :
    ((routeEdges M X) ∩ (routeEdges M Y)).card ≤
      ((routeSites M X) ∩ (routeSites M Y)).card := by
  let E := (routeEdges M X) ∩ (routeEdges M Y)
  have hinj : Set.InjOn Prod.fst (E : Set ((ℕ × A) × (ℕ × A))) := by
    intro e he f hf ht
    exact routeEdges_tail_injective M X
      (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp hf).1 ht
  have hsub : E.image Prod.fst ⊆ (routeSites M X) ∩ (routeSites M Y) := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp he
    exact Finset.mem_inter.mpr
      ⟨((mem_routeEdges M X e.1 e.2).mp hx).1,
       ((mem_routeEdges M Y e.1 e.2).mp hy).1⟩
  calc
    _ = (E.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The source EIT deterministic edge budget, for N computed from route sites. -/
theorem common_route_edges_card_le_two_levels (M : ℕ) (X Y : ℕ → A) :
    ((routeEdges M X) ∩ (routeEdges M Y)).card ≤
      2*(commonRouteLevels M X Y).card :=
  (common_route_edges_card_le_common_sites M X Y).trans
    (common_route_sites_card_le_two_levels M X Y)

end NearCritical.Section10
