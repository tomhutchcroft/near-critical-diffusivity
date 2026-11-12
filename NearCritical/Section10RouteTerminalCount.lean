module

public import NearCritical.Section10RoutePhysicalEdges

/-! The shared terminal exit fits the same 2N budget as internal common edges.
The final site has no internal outgoing edge and is therefore available for
charging the exit. This is a deterministic count, not a conditional law. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
variable {A : Type*}

def routeTerminalSite (M : ℕ) (X : ℕ → A) : ℕ × A := (M-1,X (M-1))

theorem routeTerminalSite_mem {M : ℕ} (hM : 0 < M) (X : ℕ → A) :
    routeTerminalSite M X ∈ routeSites M X := by
  exact (mem_routeSites M X (M-1) (X (M-1))).mpr ⟨by omega,Or.inl rfl⟩

theorem routeNext_terminalSite (M : ℕ) (X : ℕ → A) :
    routeNext M X (routeTerminalSite M X) = none := by
  have h : ¬ M-1+1 < M := by omega
  simp [routeNext,routeTerminalSite,h]

/-- A common exit is charged to the common final site, which no internal edge
uses as its outgoing tail. Thus no extra +1 is lost in the shared-step budget. -/
theorem common_route_edges_with_exit_card_le_two_levels (M : ℕ) (X Y : ℕ → A) :
    ((routeUnorderedEdges M X) ∩ (routeUnorderedEdges M Y)).card +
      (if 0 < M ∧ X (M-1) = Y (M-1) then 1 else 0) ≤
        2*(commonRouteLevels M X Y).card := by
  by_cases hexit : 0 < M ∧ X (M-1) = Y (M-1)
  · rw [if_pos hexit]
    let E := (routeEdges M X).filter fun e => s(e.1,e.2) ∈ routeUnorderedEdges M Y
    let T := E.image Prod.fst
    let t := routeTerminalSite M X
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
    have hcard : E.card = T.card := (Finset.card_image_of_injOn hinj).symm
    have hT : T ⊆ (routeSites M X) ∩ (routeSites M Y) := by
      intro z hz
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx,hy⟩ := Finset.mem_filter.mp he
      exact Finset.mem_inter.mpr
        ⟨((mem_routeEdges M X e.1 e.2).mp hx).1,unordered_route_edge_tail_mem hy⟩
    have ht : t ∈ (routeSites M X) ∩ (routeSites M Y) := by
      apply Finset.mem_inter.mpr
      refine ⟨routeTerminalSite_mem hexit.1 X,?_⟩
      have heq : t = routeTerminalSite M Y := by
        dsimp [t,routeTerminalSite]
        rw [hexit.2]
      rw [heq]
      exact routeTerminalSite_mem hexit.1 Y
    have hnot : t ∉ T := by
      intro htT
      obtain ⟨e,he,het⟩ := Finset.mem_image.mp htT
      have hn := ((mem_routeEdges M X e.1 e.2).mp (Finset.mem_filter.mp he).1).2
      rw [het,routeNext_terminalSite] at hn
      cases hn
    have hi : insert t T ⊆ (routeSites M X) ∩ (routeSites M Y) :=
      Finset.insert_subset_iff.mpr ⟨ht,hT⟩
    calc
      _ ≤ (E.image (fun e => s(e.1,e.2))).card+1 :=
        Nat.add_le_add_right (Finset.card_le_card hcover) 1
      _ ≤ E.card+1 := Nat.add_le_add_right Finset.card_image_le 1
      _ = (insert t T).card := by rw [Finset.card_insert_of_notMem hnot,hcard]
      _ ≤ ((routeSites M X) ∩ (routeSites M Y)).card := Finset.card_le_card hi
      _ ≤ _ := common_route_sites_card_le_two_levels M X Y
  · simpa only [if_neg hexit,Nat.add_zero] using
      common_unordered_route_edges_card_le_two_levels M X Y

end NearCritical.Section10
