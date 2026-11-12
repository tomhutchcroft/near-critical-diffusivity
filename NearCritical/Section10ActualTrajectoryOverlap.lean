import NearCritical.Section10ActualPieceOverlap
import NearCritical.Section10RouteArrival
import NearCritical.Section10RouteLabels

noncomputable section
namespace NearCritical.Section10

open scoped Classical

/-- All possible shared physical tubes. The rank interval includes the
virtual labels, which the physical-tube test removes. -/
def commonPhysicalTubes {D : ℕ} (M : ℕ) (X Y : ℕ → Fin D → ℤ) : Finset (RouteLabel D) :=
  (((Finset.Ico 0 (2*M)).image (routeLab M X)) ∩
    ((Finset.Ico 0 (2*M)).image (routeLab M Y))).filter (HasTube M)

theorem commonPhysicalTubes_card_le {D M : ℕ} (hM : 1 ≤ M) (X Y : ℕ → Fin D → ℤ) :
    (commonPhysicalTubes M X Y).card ≤ 2 * (commonRouteLevels M X Y).card := by
  have h := routeLab_common_le hM X Y
  exact (Finset.card_filter_le _ _).trans (by simpa only [commonLabelCount, zero_add] using h)

namespace NestLayout

variable {D d M : ℕ} (Λ : NestLayout D d)

/-- Site marks use the nests recorded immediately after the physical arrival. -/
def trajectorySiteMarks (X Y : ℕ → Fin D → ℤ) (a b : ℕ → Λ.X) : Finset (RSite D) :=
  (routeSites M X ∩ routeSites M Y).filter fun s =>
    ((a (routeArrivalRank X s)).1.val ∩ (b (routeArrivalRank Y s)).1.val).Nonempty

/-- Tube marks use the incoming states at the local physical move. -/
def trajectoryTubeMarks (X Y : ℕ → Fin D → ℤ) (a b : ℕ → Λ.X)
    (z : Configuration d × Configuration d) : Finset (RouteLabel D) :=
  (commonPhysicalTubes M X Y).filter fun ℓ =>
    let x := a (ℓ.rank-1)
    let y := b (ℓ.rank-1)
    Λ.firstGoodSharedTubeMark (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ x.1.val y.1.val x.2 y.2 z

/-- The edge sets used for overlap charging. The trajectory state at index
j is the state after local row j. The final exit is tracked separately. -/
structure TrajectoryFootprint (γ : SourceRoute D M) (z : Configuration d × Configuration d)
    (U : Set (Vertex d)) (state : ℕ → Λ.X) where
  inside : Finset (Sym2 (Vertex d))
  cluster : ℕ → Finset (Sym2 (Vertex d))
  bridge : ℕ → Finset (Sym2 (Vertex d))
  exitBase : Vertex d
  interior_edges : (inside : Set (Sym2 (Vertex d))) ⊆ U.sym2
  exit_outside : bondTip (exitBase,Λ.i₀) ∉ U
  covers : ∀ e ∈ inside, (∃ j < 2*M-1, e ∈ cluster j) ∨ ∃ j < 2*M-2, e ∈ bridge j
  valid : ∀ j < 2*M-1, (state j).1.val ⊆
    Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (j+1)).site
  arrival : ∀ j < 2*M-1, state j =
    state (routeArrivalRank γ.position (routeLab M γ.position (j+1)).site)
  cluster_ok : ∀ j < 2*M-1, Λ.trajectoryClusterPiece z.1 (state j) (cluster j)
  bridge_ok : ∀ j < 2*M-2, Λ.trajectoryBridgePiece z (routeLab M γ.position (j+1)) (state j) (bridge j)
  exit_ok : Λ.trajectoryExit z (state (2*M-2)) exitBase (bondTip (exitBase,Λ.i₀))

variable {Λ}

def TrajectoryFootprint.exitEdge {γ : SourceRoute D M} {z : Configuration d × Configuration d}
    {U : Set (Vertex d)} {state : ℕ → Λ.X}
    (F : Λ.TrajectoryFootprint γ z U state) : Sym2 (Vertex d) :=
  External.bondPair (F.exitBase,Λ.i₀)

def TrajectoryFootprint.edges {γ : SourceRoute D M} {z : Configuration d × Configuration d}
    {U : Set (Vertex d)} {state : ℕ → Λ.X}
    (F : Λ.TrajectoryFootprint γ z U state) : Finset (Sym2 (Vertex d)) :=
  insert F.exitEdge F.inside

theorem TrajectoryFootprint.exitEdge_notMem_inside
    {γ γ' : SourceRoute D M} {z : Configuration d × Configuration d}
    {U : Set (Vertex d)} {a b : ℕ → Λ.X}
    (F : Λ.TrajectoryFootprint γ z U a) (F' : Λ.TrajectoryFootprint γ' z U b) :
    F.exitEdge ∉ F'.inside := by
  intro h
  have hu := F'.interior_edges h
  change s(F.exitBase,bondTip (F.exitBase,Λ.i₀)) ∈ U.sym2 at hu
  exact F.exit_outside (Set.mk_mem_sym2_iff.mp hu).2

end NestLayout

variable {D t k MOff Mcoal Kdiam M : ℕ}
  (typ : TypicalParameters) (ht : 9 ≤ t) (hk : 0 < k)

local notation "Λ" => actualLayout D typ t ht k hk MOff Mcoal Kdiam M

/-- The deterministic overlap bound for two actual trajectory footprints.
A site has at most two local cluster rows and can also carry the exit edge. -/
theorem actual_trajectory_footprint_overlap (hM : 1 ≤ M)
    (z : Configuration (D+1) × Configuration (D+1)) (U : Set (Vertex (D+1)))
    (γ γ' : SourceRoute D M) (hγ : lazyRouteSurvives γ.1.1 γ.2)
    (hγ' : lazyRouteSurvives γ'.1.1 γ'.2) (a b : ℕ → (Λ).X)
    (F : (Λ).TrajectoryFootprint γ z U a) (F' : (Λ).TrajectoryFootprint γ' z U b)
    {A : ℝ} (hA : 0 ≤ A)
    (hAbound : 2 * (typ.diameterUpper * (2 * (t : ℝ)) ^ 2) ≤ A) :
    let S := (Λ).trajectorySiteMarks (M := M) γ.position γ'.position a b
    let T := (Λ).trajectoryTubeMarks (M := M) γ.position γ'.position a b z
    ((F.edges ∩ F'.edges).card : ℝ) ≤
      (2*A+1) * (S.card : ℝ) + Kdiam * (T.card : ℝ) := by
  intro S T
  let L := routeLab M γ.position
  let L' := routeLab M γ'.position
  let C := (Finset.range (2*M-1)).filter fun j =>
    (F.cluster j ∩ (F.inside ∩ F'.inside)).Nonempty
  let B := (Finset.range (2*M-2)).filter fun j =>
    (F.bridge j ∩ (F.inside ∩ F'.inside)).Nonempty
  have hsite (j j' : ℕ) (hj : j < 2*M-1) (hj' : j' < 2*M-1)
      (hs : (L (j+1)).site = (L' (j'+1)).site)
      (hmark : ((a j).1.val ∩ (b j').1.val).Nonempty) :
      (L (j+1)).site ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_inter.mpr ⟨(routeLab_site γ.position (by omega)).1, ?_⟩, ?_⟩
    · rw [hs]
      exact (routeLab_site γ'.position (by omega)).1
    · have ha := F.arrival j hj
      have hb := F'.arrival j' hj'
      change ((a (routeArrivalRank γ.position (L (j+1)).site)).1.val ∩
        (b (routeArrivalRank γ'.position (L (j+1)).site)).1.val).Nonempty
      rw [← ha, hs, ← hb]
      exact hmark
  have hHas (δ : SourceRoute D M) {j : ℕ} {x : (Λ).X}
      {E : Finset (Sym2 (Vertex (D+1)))} {e : Sym2 (Vertex (D+1))}
      (hE : (Λ).trajectoryBridgePiece z (routeLab M δ.position (j+1)) x E)
      (he : e ∈ E) : HasTube M (routeLab M δ.position (j+1)) := by
    obtain ⟨hstep,hm,_,_⟩ := hE.resolve_left (fun h => by simpa [h] using he)
    exact routeLab_hasTube δ.1.1 δ.2 hstep hm
  have hCs (j : ℕ) (hj : j ∈ C) : (L (j+1)).site ∈ S := by
    obtain ⟨hj, e, he⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_range.mp hj
    obtain ⟨hc, heInner⟩ := Finset.mem_inter.mp he
    have he' := (Finset.mem_inter.mp heInner).2
    rcases F'.covers e he' with ⟨j',hj',hc'⟩ | ⟨j',hj',hb'⟩
    · obtain ⟨hs, hm⟩ := actual_cluster_pieces_overlap typ ht hk z
        (routeLab_site_mem_box γ hγ (t := j+1) (by omega))
        (routeLab_site_mem_box γ' hγ' (t := j'+1) (by omega))
        (F.valid j hj) (F'.valid j' hj') (F.cluster_ok j hj) (F'.cluster_ok j' hj') hc hc'
      exact hsite j j' hj hj' hs hm
    · exact (Finset.disjoint_left.mp (actual_cluster_bridge_pieces_disjoint typ ht hk z
        (routeLab_site_mem_box γ hγ (t := j+1) (by omega)) (hHas γ' (F'.bridge_ok j' hj') hb')
        (F.valid j hj) (F.cluster_ok j hj) (F'.bridge_ok j' hj')) hc hb').elim
  have hBt (j : ℕ) (hj : j ∈ B) : L (j+1) ∈ T := by
    obtain ⟨hj, e, he⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_range.mp hj
    obtain ⟨hb, heInner⟩ := Finset.mem_inter.mp he
    have he' := (Finset.mem_inter.mp heInner).2
    have hB := F.bridge_ok j hj
    have hℓ := hHas γ hB hb
    rcases F'.covers e he' with ⟨j',hj',hc'⟩ | ⟨j',hj',hb'⟩
    · exact (Finset.disjoint_left.mp (actual_cluster_bridge_pieces_disjoint typ ht hk z
        (routeLab_site_mem_box γ' hγ' (t := j'+1) (by omega)) hℓ (F'.valid j' hj')
        (F'.cluster_ok j' hj') hB) hc' hb).elim
    · obtain ⟨hsame, hm⟩ := actual_bridge_pieces_overlap typ ht hk z hℓ
        (hHas γ' (F'.bridge_ok j' hj') hb') hB (F'.bridge_ok j' hj') hb hb'
      have htime : j = j' := by
        have h := congrArg RouteLabel.rank hsame
        simp only [L, L', rank_routeLab hM] at h
        omega
      subst j'
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨?_,?_⟩, hℓ⟩,?_⟩
      · exact Finset.mem_image.mpr ⟨j+1, Finset.mem_Ico.mpr ⟨by omega,by omega⟩,rfl⟩
      · exact Finset.mem_image.mpr ⟨j+1, Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hsame.symm⟩
      · change (Λ).firstGoodSharedTubeMark (refineReveal (Λ).ρ₀ (Λ).S₀ z) (L (j+1))
          (a ((L (j+1)).rank-1)).1.val (b ((L (j+1)).rank-1)).1.val
          (a ((L (j+1)).rank-1)).2 (b ((L (j+1)).rank-1)).2 z
        simpa only [L, rank_routeLab hM, Nat.add_sub_cancel] using hm
  have hCcard : C.card ≤ 2*S.card := by
    have hc : C.card ≤ (S.product (Finset.range 2)).card := by
      apply Finset.card_le_card_of_injOn (fun j => ((L (j+1)).site,(j+1)%2))
      · intro j hj
        exact Finset.mem_coe.mpr (Finset.mem_product.mpr
          ⟨hCs j hj,Finset.mem_range.mpr (Nat.mod_lt _ (by decide))⟩)
      · intro j hj j' hj' heq
        have hjb := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj : j ∈ C)).1
        have hjb' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj' : j' ∈ C)).1
        have hjl := (routeLab_site (M := M) γ.position (t := j+1) (by omega)).2
        have hjl' := (routeLab_site (M := M) γ.position (t := j'+1) (by omega)).2
        have hlevel := congrArg Prod.fst (Prod.mk.inj heq).1
        change (L (j+1)).site.1 = (L (j'+1)).site.1 at hlevel
        rw [hjl,hjl'] at hlevel
        have hpar := (Prod.mk.inj heq).2
        omega
    rwa [Finset.product_eq_sprod, Finset.card_product, Finset.card_range, Nat.mul_comm] at hc
  have hBcard : B.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun j => L (j+1))
    · intro j hj
      exact Finset.mem_coe.mpr (hBt j hj)
    · intro j _ j' _ heq
      have h := congrArg RouteLabel.rank heq
      simp only [L, rank_routeLab hM] at h
      omega
  have hInner : F.inside ∩ F'.inside ⊆ C.biUnion F.cluster ∪ B.biUnion F.bridge := by
    intro e he
    rcases F.covers e (Finset.mem_inter.mp he).1 with ⟨j,hj,hc⟩ | ⟨j,hj,hb⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,e,Finset.mem_inter.mpr ⟨hc,he⟩⟩,hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,e,Finset.mem_inter.mpr ⟨hb,he⟩⟩,hb⟩)
  have hCbudget : ((C.biUnion F.cluster).card : ℝ) ≤ 2*A*(S.card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ C, ((F.cluster j).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ C, A := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj, e, he⟩ := Finset.mem_filter.mp hj
        have h := F.cluster_ok j (Finset.mem_range.mp hj)
        exact (h.resolve_left (fun hh => by simpa [hh] using (Finset.mem_inter.mp he).1)).1.trans hAbound
      _ = (C.card : ℝ) * A := by simp
      _ ≤ _ := by
        have h : (C.card : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hCcard
        calc (C.card : ℝ) * A ≤ (2 * (S.card : ℝ)) * A := mul_le_mul_of_nonneg_right h hA
          _ = _ := by ring
  have hBbudget : ((B.biUnion F.bridge).card : ℝ) ≤ Kdiam*(T.card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ B, ((F.bridge j).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ B, (Kdiam : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj, e, he⟩ := Finset.mem_filter.mp hj
        have h := F.bridge_ok j (Finset.mem_range.mp hj)
        exact (h.resolve_left (fun hh => by simpa [hh] using (Finset.mem_inter.mp he).1)).2.2.1
      _ = (Kdiam : ℝ) * (B.card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hBcard) (Nat.cast_nonneg _)
  let E := ({F.exitEdge} : Finset (Sym2 (Vertex (D+1)))) ∩ {F'.exitEdge}
  have hEbudget : (E.card : ℝ) ≤ S.card := by
    by_cases h : F.exitEdge = F'.exitEdge
    · have hj : 2*M-2 < 2*M-1 := by omega
      obtain ⟨hs, hm⟩ := actual_exit_pieces_overlap typ ht hk z
        (routeLab_site_mem_box γ hγ (t := (2*M-2)+1) (by omega))
        (routeLab_site_mem_box γ' hγ' (t := (2*M-2)+1) (by omega))
        (F.valid _ hj) (F'.valid _ hj) F.exit_ok F'.exit_ok h
      have hmem := hsite _ _ hj hj hs hm
      have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨_, hmem⟩
      simpa [E,h] using (show (1:ℝ) ≤ (S.card : ℝ) by exact_mod_cast hcard)
    · simp [E, h]
  have hFull : F.edges ∩ F'.edges ⊆ (F.inside ∩ F'.inside) ∪ E := by
    intro e he
    obtain ⟨hl,hr⟩ := Finset.mem_inter.mp he
    rw [NestLayout.TrajectoryFootprint.edges, Finset.mem_insert] at hl hr
    rcases hl with rfl | hl
    · rcases hr with hr | hr
      · exact Finset.mem_union_right _ (by simp [E,hr])
      · exact (F.exitEdge_notMem_inside F' hr).elim
    · rcases hr with rfl | hr
      · exact (F'.exitEdge_notMem_inside F hl).elim
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hl,hr⟩)
  have h1 : ((F.edges ∩ F'.edges).card : ℝ) ≤ ((F.inside ∩ F'.inside).card : ℝ) + E.card := by
    exact_mod_cast (Finset.card_le_card hFull).trans (Finset.card_union_le _ _)
  have h2 : ((F.inside ∩ F'.inside).card : ℝ) ≤
      ((C.biUnion F.cluster).card : ℝ) + (B.biUnion F.bridge).card := by
    exact_mod_cast (Finset.card_le_card hInner).trans (Finset.card_union_le _ _)
  linarith

end NearCritical.Section10
