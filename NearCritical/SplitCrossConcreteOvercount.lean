module

public import NearCritical.SplitCrossConcreteMoats
public import NearCritical.SplitCrossConcreteIncidence
public import NearCritical.SplitCrossNodeSeparation

/-! For fixed terminal positions two realized placements of the concrete
tree have corresponding branch sites at bounded distance. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode
open scoped Classical

theorem concreteCrossingLayout_arm_mem {d t : ℕ} (ht : 64 ≤ t) (hd : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (x : Vertex d) (axis : Fin d) (R : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (v : CrossingBranch (4 * d)) (j : Fin 3) (k : ℕ) (hk : k ≤ R + 1) :
    rayPt (b v.val) (crossingPortAxis hd j) k ∈ (concreteCrossingLayout hd hL t x R).Λ := by
  rw [rayPt_eq_starTip]
  exact crossingEdgeRegion_subset_envelope ht v.val
    (branchBox_subset_incoming_region ht axis v.val
      (branchBox_offset_subset hts htl x axis v.val ((mem_crossingBranches _).mpr v.property)
        (hb v.val) (starTip_mem_box _ _ hk)))

private theorem dist_of_rayPt_eq {d : ℕ} {a b : Vertex d} {i j : Fin d} {k l n : ℕ}
    (hk : k ≤ n) (hl : l ≤ n) (h : rayPt a i k = rayPt b j l) :
    dist a b ≤ 2 * (n : ℝ) := by
  rw [rayPt_eq_starTip, rayPt_eq_starTip] at h
  calc
    dist a b ≤ dist a (starTip a i k) + dist (starTip a i k) b := dist_triangle _ _ _
    _ = (k : ℝ) + (l : ℝ) := by
      rw [dist_comm a, dist_starTip_center, h, dist_starTip_center]
    _ ≤ 2 * (n : ℝ) := by
      have hk' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      have hl' : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hl
      linarith

/-- The fixed-terminal overcount bound on the position of each branch. -/
theorem concreteCrossingLayout_real_close {d t : ℕ} (ht : 4096 ≤ t)
    (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hgap : 2 * ((R + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (b b' : SplitTreeNode (4 * d) → Vertex d)
    (hb : ∀ v, b v ∈ nodeSites t x axis v) (hb' : ∀ v, b' v ∈ nodeSites t x axis v)
    (y : CrossingTerminal (4 * d) → Vertex d)
    {hpos : ∀ e ∈ (concreteCrossingLayout hd hL t x R).edges,
      (concreteCrossingLayout hd hL t x R).pos (fun v => b v.val) y e.1 ∈
        (concreteCrossingLayout hd hL t x R).Uout (fun v => b v.val)}
    {hpos' : ∀ e ∈ (concreteCrossingLayout hd hL t x R).edges,
      (concreteCrossingLayout hd hL t x R).pos (fun v => b' v.val) y e.1 ∈
        (concreteCrossingLayout hd hL t x R).Uout (fun v => b' v.val)}
    {θ : Configuration d}
    (hθ : θ ∈ (concreteCrossingLayout hd hL t x R).Real (fun v => b v.val) y hpos)
    (hθ' : θ ∈ (concreteCrossingLayout hd hL t x R).Real (fun v => b' v.val) y hpos')
    (cut : CrossingBranch (4 * d)) :
    dist (b cut.val) (b' cut.val) ≤ 2 * ((R + 1 : ℕ) : ℝ) := by
  by_contra! hfar
  let L := concreteCrossingLayout hd hL t x R
  have hΛ : ∀ (v : CrossingBranch (4 * d)) (j : Fin 3) (k : ℕ), k ≤ L.R →
      rayPt (b v.val) (L.ax j) k ∈ L.Λ :=
    concreteCrossingLayout_arm_mem (by omega) hd hL x axis R hts htl b hb
  have hΛ' : ∀ (v : CrossingBranch (4 * d)) (j : Fin 3) (k : ℕ), k ≤ L.R →
      rayPt (b' v.val) (L.ax j) k ∈ L.Λ :=
    concreteCrossingLayout_arm_mem (by omega) hd hL x axis R hts htl b' hb'
  have hRm : ∀ j k, k ≤ L.R → rayPt (b' cut.val) (L.ax j) k ∉ L.Rm (fun v => b v.val) := by
    intro j k hk hm
    obtain ⟨v, _, hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨i, _, hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hm
    have hclose := dist_of_rayPt_eq (Nat.le_of_lt (Finset.mem_range.mp hl)) hk he
    by_cases hv : v = cut
    · subst v
      exact (not_lt_of_ge hclose) hfar
    · have hsep := nodeSites_dist_of_ne (by omega : 2 ≤ d) ht hx axis
        (fun h => hv (Subtype.ext h)) (hb v.val) (hb' cut.val)
      exact (not_lt_of_ge (hsep.trans hclose)) hgap
  have hsep' : ∀ (u u' : CrossingBranch (4 * d)), u ≠ u' → ∀ j j' k k',
      k < L.R → k' < L.R → rayPt (b' u.val) (L.ax j) k ≠ rayPt (b' u'.val) (L.ax j') k' := by
    intro u u' hne j j' k k' hk hk' he
    have hclose := dist_of_rayPt_eq (Nat.le_of_lt hk) (Nat.le_of_lt hk') he
    have hsep := nodeSites_dist_of_ne (by omega : 2 ≤ d) ht hx axis
      (fun h => hne (Subtype.ext h)) (hb' u.val) (hb' u'.val)
    exact (not_lt_of_ge (hsep.trans hclose)) hgap
  obtain ⟨P, E, he, hp⟩ := concreteCrossingLayout_side_witnesses hd hL t x R cut
  have hfix (k : Fin 3) : L.pos (fun v => b v.val) y (P k) = L.pos (fun v => b' v.val) y (P k) := by
    rcases hp k with h | ⟨v, h⟩ <;> simp only [h, Layout.pos]
  exact L.real_real_false hθ hθ' cut
    (concreteCrossingLayout_preconnected hd hL t x R) hΛ hΛ' hRm hsep'
    (concreteCrossingLayout_tip_edge hd hL t x R)
    (fun u => crossingSideCode (crossingSide hL cut.val u.val))
    (fun e => crossingSideCode (crossingSide hL cut.val (crossingPortNode e.2)))
    (concreteCrossingLayout_side_compatible hd hL t x R cut) P E he hfix

private theorem mem_translateSites_of_dist_le {d n : ℕ} {a b : Vertex d}
    (h : dist a b ≤ (n : ℝ)) : b ∈ translateSites a (centeredBox d n) := by
  apply Finset.mem_image.mpr
  refine ⟨b - a, mem_centeredBox.mpr ?_, by abel⟩
  intro j
  have hj := (dist_le_pi_dist a b j).trans h
  rw [Int.dist_eq, abs_le] at hj
  have hlo : -((n : ℕ) : ℤ) ≤ a j - b j := by exact_mod_cast hj.1
  have hhi : a j - b j ≤ (n : ℤ) := by exact_mod_cast hj.2
  simp only [Pi.sub_apply]
  omega

private theorem branch_family_card_le {d L n : ℕ} (A : Finset (CrossingBranch L → Vertex d))
    (h : ∀ a ∈ A, ∀ b ∈ A, ∀ v, dist (a v) (b v) ≤ (n : ℝ)) :
    A.card ≤ ((2 * n + 1) ^ d) ^ Fintype.card (CrossingBranch L) := by
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    let B := Fintype.piFinset fun v : CrossingBranch L => translateSites (a v) (centeredBox d n)
    have hab : A ⊆ B := by
      intro b hb
      exact Fintype.mem_piFinset.mpr (fun v => mem_translateSites_of_dist_le (h a ha b hb v))
    calc
      A.card ≤ B.card := Finset.card_le_card hab
      _ = _ := by simp [B, Fintype.card_piFinset, card_translateSites, card_centeredBox_exact]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

/-- A uniform bound on the number of realized branch placements for fixed terminals. -/
theorem concreteCrossingLayout_real_multiplicity {d t : ℕ} (ht : 4096 ≤ t)
    (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hgap : 2 * ((R + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (y : CrossingTerminal (4 * d) → Vertex d) (θ : Configuration d)
    (S : Finset (CrossingBranch (4 * d) → Vertex d))
    (hS : ∀ β ∈ S, ∃ b : SplitTreeNode (4 * d) → Vertex d,
      (∀ v, b v ∈ nodeSites t x axis v) ∧ (fun v : CrossingBranch (4 * d) => b v.val) = β) :
    let L := concreteCrossingLayout hd hL t x R
    (S.filter fun β => ∃ hpos, θ ∈ L.Real β y hpos).card ≤
      ((2 * (2 * (R + 1)) + 1) ^ d) ^ Fintype.card (CrossingBranch (4 * d)) := by
  intro L
  apply branch_family_card_le
  intro β hβ β' hβ' v
  obtain ⟨hβ, hpos, hθ⟩ := Finset.mem_filter.mp hβ
  obtain ⟨hβ', hpos', hθ'⟩ := Finset.mem_filter.mp hβ'
  obtain ⟨b, hb, he⟩ := hS β hβ
  obtain ⟨b', hb', he'⟩ := hS β' hβ'
  subst β
  subst β'
  push_cast
  simpa only [Nat.cast_add, Nat.cast_one] using
    concreteCrossingLayout_real_close ht hd hL x hx axis R hts htl hgap b b' hb hb' y hθ hθ' v

end NearCritical.SplitCrossDirect
