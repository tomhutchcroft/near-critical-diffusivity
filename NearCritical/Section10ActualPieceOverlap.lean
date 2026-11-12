import NearCritical.Section10ActualTrajectoryPieces
import NearCritical.Section10ActualTubeSupport
import NearCritical.Section10OverlapLocations
import NearCritical.Section10FirstGoodBridgeMark
import NearCritical.Section10RevealPositivity

noncomputable section
namespace NearCritical.Section10

open scoped Classical

variable {D t k MOff Mcoal Kdiam M : ℕ}
  (typ : TypicalParameters) (ht : 9 ≤ t) (hk : 0 < k)

local notation "Λ" => actualLayout D typ t ht k hk MOff Mcoal Kdiam M

private theorem actual_piece_cubes_disjoint :
    Pairwise fun s s' : RSite D => Disjoint ((Λ).Q s) ((Λ).Q s') := by
  intro s s' hne
  exact typicalCube_disjoint_of_ne (t := t) (a := vecSite s) (b := vecSite s')
    (by omega) (fun h => hne (vecSite_injective h))

/-- A common cluster edge identifies a common site and an actual shared
representative in its two incoming nests. -/
theorem actual_cluster_pieces_overlap
    (z : Configuration (D+1) × Configuration (D+1)) {s s' : RSite D}
    (hs : s ∈ (Λ).siteBox) (hs' : s' ∈ (Λ).siteBox) {x y : (Λ).X}
    (hx : x.1.val ⊆ (Λ).fam (refineReveal (Λ).ρ₀ (Λ).S₀ z) s)
    (hy : y.1.val ⊆ (Λ).fam (refineReveal (Λ).ρ₀ (Λ).S₀ z) s')
    {C C' : Finset (Sym2 (Vertex (D+1)))} {e : Sym2 (Vertex (D+1))}
    (hC : (Λ).trajectoryClusterPiece z.1 x C) (hC' : (Λ).trajectoryClusterPiece z.1 y C')
    (he : e ∈ C) (he' : e ∈ C') : s = s' ∧ (x.1.val ∩ y.1.val).Nonempty := by
  obtain ⟨_, c, hc, hce⟩ := hC.resolve_left (fun h => by simpa [h] using he)
  obtain ⟨_, c', hc', hce'⟩ := hC'.resolve_left (fun h => by simpa [h] using he')
  have ha := hx hc
  have ha' := hy hc'
  rw [(Λ).fam_eq z hs] at ha
  rw [(Λ).fam_eq z hs'] at ha'
  obtain ⟨hsame, hrep⟩ := common_cluster_edge_identifies_cluster z.1 (Λ).Q
    (actual_piece_cubes_disjoint typ ht hk)
    ((mem_typicalClusterFamily _ _ _ _ _).mp ha).1
    ((mem_typicalClusterFamily _ _ _ _ _).mp ha').1 (hce he) (hce' he')
  exact ⟨hsame, c, Finset.mem_inter.mpr ⟨hc, hrep.symm ▸ hc'⟩⟩

/-- A common exit edge identifies a common site and a common representative
in the nests that issue it. -/
theorem actual_exit_pieces_overlap
    (z : Configuration (D+1) × Configuration (D+1)) {s s' : RSite D}
    (hs : s ∈ (Λ).siteBox) (hs' : s' ∈ (Λ).siteBox) {x y : (Λ).X}
    (hx : x.1.val ⊆ (Λ).fam (refineReveal (Λ).ρ₀ (Λ).S₀ z) s)
    (hy : y.1.val ⊆ (Λ).fam (refineReveal (Λ).ρ₀ (Λ).S₀ z) s')
    {v w v' w' : Vertex (D+1)} (hv : (Λ).trajectoryExit z x v w)
    (hv' : (Λ).trajectoryExit z y v' w')
    (he : External.bondPair (v, (Λ).i₀) = External.bondPair (v', (Λ).i₀)) :
    s = s' ∧ (x.1.val ∩ y.1.val).Nonempty := by
  obtain ⟨_, _, c, hc, hvc⟩ := hv
  obtain ⟨_, _, c', hc', hvc'⟩ := hv'
  have ha := hx hc
  have ha' := hy hc'
  rw [(Λ).fam_eq z hs] at ha
  rw [(Λ).fam_eq z hs'] at ha'
  obtain ⟨hsame, hrep⟩ := common_terminal_edge_identifies_cluster z.1 (Λ).i₀ (Λ).Q
    (actual_piece_cubes_disjoint typ ht hk)
    ((mem_typicalClusterFamily _ _ _ _ _).mp ha).1
    ((mem_typicalClusterFamily _ _ _ _ _).mp ha').1 hvc hvc' he
  exact ⟨hsame, c, Finset.mem_inter.mpr ⟨hc, hrep.symm ▸ hc'⟩⟩

private theorem actual_bridge_piece_in_tube
    (z : Configuration (D+1) × Configuration (D+1)) {ℓ : RouteLabel D} (hℓ : HasTube M ℓ)
    {x : (Λ).X} {B : Finset (Sym2 (Vertex (D+1)))} (hB : (Λ).trajectoryBridgePiece z ℓ x B) :
    (B : Set (Sym2 (Vertex (D+1)))) ⊆
      (coarseTubeVertices (2 * (t : ℝ)) (vecSite ℓ.site) (dirOf ℓ)).sym2 := by
  intro e he
  have h := (hB.resolve_left (fun h => by simpa [h] using he)).2.2.2 e he
  rw [Set.mem_sym2_iff_subset, ← actual_layout_side_union_eq_coarseTube typ t ht k hk MOff Mcoal Kdiam M hℓ]
  intro v hv
  exact Finset.mem_union.mp (section9SprinklingCluster_subset _ _ _ _ _ _ _ _ _ _ _ (h.1 v hv))

/-- Common bridge edges are in the same physical tube and force its
whole-nest intersection mark. -/
theorem actual_bridge_pieces_overlap
    (z : Configuration (D+1) × Configuration (D+1)) {ℓ ℓ' : RouteLabel D}
    (hℓ : HasTube M ℓ) (hℓ' : HasTube M ℓ') {x y : (Λ).X}
    {B B' : Finset (Sym2 (Vertex (D+1)))} {e : Sym2 (Vertex (D+1))}
    (hB : (Λ).trajectoryBridgePiece z ℓ x B) (hB' : (Λ).trajectoryBridgePiece z ℓ' y B')
    (he : e ∈ B) (he' : e ∈ B') :
    ℓ = ℓ' ∧ (Λ).firstGoodSharedTubeMark (refineReveal (Λ).ρ₀ (Λ).S₀ z) ℓ x.1.val y.1.val x.2 y.2 z := by
  have hsame : ℓ = ℓ' := by
    by_contra hne
    exact tube_key_ne hℓ hℓ' hne (common_bridge_edge_identifies_tube (by positivity)
      (actual_bridge_piece_in_tube typ ht hk z hℓ hB he)
      (actual_bridge_piece_in_tube typ ht hk z hℓ' hB' he'))
  subst ℓ'
  have hL : (Λ).Mid ℓ ⊆ (Λ).L ℓ := by
    rw [actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
      actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ]
    apply translateSites_mono
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have hQ : Disjoint ((Λ).Mid ℓ : Set (Vertex (D+1))) ((Λ).Q ℓ.site : Set (Vertex (D+1))) := by
    rw [actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
      actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ]
    apply Finset.disjoint_coe.mpr
    exact (Finset.disjoint_image (add_right_injective _)).mpr
      (section9FiniteMiddle_disjoint_first _ (by omega))
  refine ⟨rfl, ((Λ).firstGoodSharedTubeMark_iff_or_bridge ℓ x.1.val y.1.val x.2 y.2 z hL hQ).2 ?_⟩
  obtain ⟨v,hv⟩ : ∃ v, v ∈ e := by
    induction e using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
  have h := (hB.resolve_left (fun h => by simpa [h] using he)).2.2.2 e he
  have h' := (hB'.resolve_left (fun h => by simpa [h] using he')).2.2.2 e he'
  exact ⟨v, Finset.mem_inter.mpr ⟨h.1 v hv, h'.1 v hv⟩⟩

/-- The cluster pieces and bridge pieces of the actual construction are
edge-disjoint, including at the two incident cubes. -/
theorem actual_cluster_bridge_pieces_disjoint
    (z : Configuration (D+1) × Configuration (D+1)) {s : RSite D} (hs : s ∈ (Λ).siteBox)
    {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) {x y : (Λ).X}
    (hx : x.1.val ⊆ (Λ).fam (refineReveal (Λ).ρ₀ (Λ).S₀ z) s)
    {C B : Finset (Sym2 (Vertex (D+1)))}
    (hC : (Λ).trajectoryClusterPiece z.1 x C) (hB : (Λ).trajectoryBridgePiece z ℓ y B) :
    Disjoint C B := by
  apply Finset.disjoint_left.mpr
  intro e he hb
  obtain ⟨_, c, hc, hcover⟩ := hC.resolve_left (fun h => by simpa [h] using he)
  have ha := hx hc
  rw [(Λ).fam_eq z hs] at ha
  have hCtyp := (mem_typicalClusterFamily _ _ _ _ _).mp ha
  have hCQ : (c : Set (Vertex (D+1))) ⊆ ((Λ).Q s : Set (Vertex (D+1))) :=
    Finset.coe_subset.mpr (typicalCluster_subset_cube _ _ _ _ ha)
  have hCF : (c : Set (Vertex (D+1))) ⊆ ((Λ).Fat ((Λ).ρ₀ z) s : Set (Vertex (D+1))) := by
    rw [(Λ).Fat_realised z hs]
    exact Finset.coe_subset.mpr hCtyp.2.1
  let T := coarseTubeVertices (2 * (t : ℝ)) (vecSite ℓ.site) (dirOf ℓ)
  have hcases : Disjoint (c : Set (Vertex (D+1))) T ∨
      ((c : Set (Vertex (D+1))) ⊆ ((Λ).Q ℓ.site : Set (Vertex (D+1))) ∧
        (c : Set (Vertex (D+1))) ⊆ ((Λ).Fat ((Λ).ρ₀ z) ℓ.site : Set (Vertex (D+1)))) ∨
      ((c : Set (Vertex (D+1))) ⊆ ((Λ).Q ℓ.target : Set (Vertex (D+1))) ∧
        (c : Set (Vertex (D+1))) ⊆ ((Λ).Fat ((Λ).ρ₀ z) ℓ.target : Set (Vertex (D+1)))) := by
    rcases eq_or_ne s ℓ.site with rfl | hnear
    · exact Or.inr (Or.inl ⟨hCQ,hCF⟩)
    rcases eq_or_ne s ℓ.target with rfl | hfar
    · exact Or.inr (Or.inr ⟨hCQ,hCF⟩)
    have hfar' : vecSite s ≠ vecSite ℓ.site + Pi.single (dirOf ℓ) 1 := by
      rw [← dirOf_spec hℓ]
      exact fun h => hfar (vecSite_injective h)
    exact Or.inl ((coarseTube_disjoint_nonincident_typicalCube (by omega : 0 < t)
      (vecSite ℓ.site) (vecSite s) (dirOf ℓ) (fun h => hnear (vecSite_injective h)) hfar').symm.mono_left hCQ)
  have hAvoid : ∀ f ∈ B, f ∉ exploredEdgeSet ((Λ).Q ℓ.site) ((Λ).Fat ((Λ).ρ₀ z) ℓ.site) ∪
      exploredEdgeSet ((Λ).Q ℓ.target) ((Λ).Fat ((Λ).ρ₀ z) ℓ.target) := by
    intro f hf
    exact ((hB.resolve_left (fun h => by simpa [h] using hb)).2.2.2 f hf).2
  exact Set.disjoint_left.mp (cluster_bridge_support_disjoint z.1 _ T _ _ _ _ B
    (actual_bridge_piece_in_tube typ ht hk z hℓ hB) hAvoid hcases) (hcover he) hb

end NearCritical.Section10
