module

public import NearCritical.Section10RoutePhysicalEdges
public import NearCritical.Section10PhaseHistory
public import NearCritical.Section10LatticeRule

/-! A site contributes its second arrival and a shared internal tube
contributes its joint reveal. Initial entanglement is charged to the common
start site, and an exit adds no tube entanglement. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- The rank at which an individual route first reaches a site. At positive
levels it reaches the old position vertically and, if distinct, the new
position horizontally. -/
def routeArrivalRank {D : ℕ} (X : ℕ → Fin D → ℤ) (z : RSite D) : ℕ :=
  if z.1 = 0 then 0 else if z.2 = X (z.1-1) then 2*z.1-1 else 2*z.1

theorem routeArrivalRank_spec {D M : ℕ} (X : ℕ → Fin D → ℤ) {z : RSite D}
    (hz : z ∈ routeSites M X) :
    routeArrivalRank X z < 2*M ∧
      (routeLab M X (routeArrivalRank X z)).target = z ∧
      (z.1 ≠ 0 → (routeLab M X (routeArrivalRank X z)).site ≠ z) := by
  obtain ⟨j, x⟩ := z
  obtain ⟨hj, hsite⟩ := (mem_routeSites M X j x).mp hz
  by_cases hj₀ : j = 0
  · subst j
    have hX : x = X 0 := by simpa using hsite
    simp [routeArrivalRank, routeLab, RouteLabel.target, hX] <;> omega
  by_cases hold : x = X (j-1)
  · have ht : 2*j-1 < 2*M := by omega
    have h0 : 2*j-1 ≠ 0 := by omega
    have hend : 2*j-1 ≠ 2*M-1 := by omega
    have hodd : (2*j-1) % 2 = 1 := by omega
    have hdiv : (2*j-1-1)/2 = j-1 := by omega
    simp only [routeArrivalRank, Prod.fst, Prod.snd, if_neg hj₀, if_pos hold]
    rw [routeLab, if_neg h0, if_neg (by omega : ¬2*M ≤ 2*j-1), if_neg hend, if_pos hodd, hdiv]
    refine ⟨ht, ?_, ?_⟩
    · simp [RouteLabel.target, hold, show j-1+1 = j by omega]
    · intro _ he
      have hlev := congrArg Prod.fst he
      simp only [RouteLabel.site] at hlev
      omega
  · have hX : x = X j := hsite.resolve_right hold
    have ht : 2*j < 2*M := by omega
    have h0 : 2*j ≠ 0 := by omega
    have hend : 2*j ≠ 2*M-1 := by omega
    have heven : (2*j) % 2 ≠ 1 := by omega
    have hdiv : (2*j)/2 = j := by omega
    simp only [routeArrivalRank, Prod.fst, Prod.snd, if_neg hj₀, if_neg hold]
    rw [routeLab, if_neg h0, if_neg (by omega : ¬2*M ≤ 2*j), if_neg hend, if_neg heven, hdiv]
    exact ⟨ht, by simp [RouteLabel.target, hX], fun _ he => hold ((congrArg Prod.snd he).symm)⟩

/-- Candidate times for an entanglement in the ordered joint history. -/
def routeEntanglementTimes {A : Type*} (M : ℕ) (X Y : ℕ → A)
    (secondArrival : (ℕ × A) → ℕ) (sharedReveal : Sym2 (ℕ × A) → ℕ) : Finset ℕ :=
  ((routeSites M X ∩ routeSites M Y).image secondArrival) ∪
    ((routeUnorderedEdges M X ∩ routeUnorderedEdges M Y).image sharedReveal)

/-- The common start, when present, is already among the common sites.
The source bound of 4N+1 therefore holds with 4N for this assignment. -/
theorem routeEntanglementTimes_card_le {A : Type*} (M : ℕ) (X Y : ℕ → A)
    (secondArrival : (ℕ × A) → ℕ) (sharedReveal : Sym2 (ℕ × A) → ℕ) :
    (routeEntanglementTimes M X Y secondArrival sharedReveal).card ≤
      4 * (commonRouteLevels M X Y).card := by
  unfold routeEntanglementTimes
  refine (Finset.card_union_le _ _).trans ?_
  have hS := Finset.card_image_le (s := routeSites M X ∩ routeSites M Y) (f := secondArrival)
  have hE := Finset.card_image_le (s := routeUnorderedEdges M X ∩ routeUnorderedEdges M Y)
    (f := sharedReveal)
  have hs := hS.trans (common_route_sites_card_le_two_levels M X Y)
  have he := hE.trans (common_unordered_route_edges_card_le_two_levels M X Y)
  omega

/-- There are no site or tube entanglements when the routes have no common
level, including the initial pair. -/
theorem routeEntanglementTimes_eq_empty_of_no_common {A : Type*}
    (M : ℕ) (X Y : ℕ → A) (secondArrival : (ℕ × A) → ℕ) (sharedReveal : Sym2 (ℕ × A) → ℕ)
    (hN : (commonRouteLevels M X Y).card = 0) :
    routeEntanglementTimes M X Y secondArrival sharedReveal = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := routeEntanglementTimes_card_le M X Y secondArrival sharedReveal
  omega

end NearCritical.Section10
