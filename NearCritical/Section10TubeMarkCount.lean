import NearCritical.Section10ActualTrajectoryOverlap
import NearCritical.Section10SharedArrivalRecurrence
import NearCritical.Section10MarkedCount
import NearCritical.Section10ArrivalTubeGeometry

noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

set_option maxHeartbeats 500000 in
/-- Sum the actual tube estimates over all common physical tubes, after
carrying each mark from its own clock to the terminal history. -/
theorem firstGood_terminal_tube_count_mass_le
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ) (hM : 1 ≤ M)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (x : Λ.X × Λ.X) {E : ℝ} (hE : 0 ≤ E)
    (hTube : ∀ j < 2*M, routeLab M γ.position j = routeLab M γ'.position j →
      HasTube M (routeLab M γ.position j) →
      Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G x j ≤ E) :
    let S := jointRoutePrefix M γ.position γ'.position (2*M)
    let L (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    markedPrefixMass p q (L γ) (L γ') S 0 0 x
      (fun h z => (((commonPhysicalTubes M γ.position γ'.position).filter (fun ℓ =>
        Λ.mergedTubeMark G ℓ false S (ℓ.rank-1) (ℓ.rank-1) h z)).card : ℝ)) /
        ρ ^ sharedCount S ≤
      2 * ((commonRouteLevels M γ.position γ'.position).card:ℝ) * E := by
  intro S L
  let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let T := commonPhysicalTubes M γ.position γ'.position
  let H := NestTrace (Λ.X × Λ.X) S.length
  let Mark (ℓ : RouteLabel D) (h : H) z := Λ.mergedTubeMark G ℓ false S (ℓ.rank-1) (ℓ.rank-1) h z
  have hk (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (L δ j u v) :=
    stepKernel_isLocal _ _ _ _ v
  have hmark (ℓ : RouteLabel D) (hℓ : ℓ ∈ T) :
      markedPrefixMass p q (L γ) (L γ') S 0 0 x
        (fun h z => if Mark ℓ h z then 1 else 0) / ρ ^ sharedCount S ≤ E := by
    obtain ⟨hmem,hTubeℓ⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨hLeft,hRight⟩ := Finset.mem_inter.mp hmem
    obtain ⟨j,hj,hl⟩ := Finset.mem_image.mp hLeft
    obtain ⟨j',hj',hr⟩ := Finset.mem_image.mp hRight
    have hjM : j < 2*M := (Finset.mem_Ico.mp hj).2
    have hRank : ℓ.rank = j := (congrArg RouteLabel.rank hl.symm).trans (rank_routeLab hM _ _)
    have hRank' : ℓ.rank = j' := (congrArg RouteLabel.rank hr.symm).trans (rank_routeLab hM _ _)
    have hjEq := hRank.symm.trans hRank'
    have heq : routeLab M γ.position j = routeLab M γ'.position j :=
      hl.trans (((congrArg (routeLab M γ'.position) hjEq).trans hr).symm)
    have hTubeJ : HasTube M (routeLab M γ.position j) := by rw [hl]; exact hTubeℓ
    have hj₀ := (routeLab_hasTube_clock hM γ.position hjM hTubeJ).1
    let s := jointRoutePrefix M γ.position γ'.position (j+1)
    obtain ⟨r,he⟩ := jointRoutePrefix_extends hM γ.position γ'.position (show j+1 ≤ 2*M by omega)
    change S = s ++ r at he
    have hFresh : PairFresh (B γ) (B γ') (s ++ r) 0 0 (Λ.S₀ G.1) :=
      he ▸ Rule.route_pair_fresh hM γ γ' G (2*M) (2*M) 0 0
    obtain ⟨hcl,hcr⟩ := jointRoutePrefix_clocks M γ.position γ'.position (j+1)
    change leftCount s = j+1 at hcl
    change rightCount s = j+1 at hcr
    have hRead : Λ.Bl₀ G.1 ℓ ⊆ mergedTraceBlocks (B γ) (B γ') s 0 0 := by
      rw [← hl]
      simpa only [Nat.zero_add] using
        leftBlock_subset_mergedTraceBlocks (B γ) (B γ') s 0 0 j (by rw [hcl]; omega)
    have hcarry := Λ.firstGood_tube_mark_mass_suffix_le p q ρ κ hκ hs hsite hρ γ γ' G
      s r x ℓ (ℓ.rank-1) (ℓ.rank-1) (by rw [hcl,hRank]; omega) (by rw [hcr,hRank]; omega) hFresh hRead
    rw [← he] at hcarry
    refine hcarry.trans ?_
    have h := hTube j hjM heq hTubeJ
    change markedPrefixMass p q (L γ) (L γ') s 0 0 x
      (fun h z => if Λ.mergedTubeMark G ℓ false s (ℓ.rank-1) (ℓ.rank-1) h z then 1 else 0) /
        ρ ^ sharedCount s ≤ E
    rw [hRank,← hl]
    exact h
  have hh := markedPrefixMass_card_filter_le p q (B γ) (B γ') (L γ) (L γ')
    (hk γ) (hk γ') S 0 0 x T (fun ℓ => Λ.Bl₀ G.1 ℓ) Mark
    (fun ℓ _ h => Λ.mergedTubeMark_readsOnly G ℓ false S (ℓ.rank-1) (ℓ.rank-1) h)
    ρ E hmark
  refine hh.trans (mul_le_mul_of_nonneg_right ?_ hE)
  dsimp only [T]
  exact_mod_cast commonPhysicalTubes_card_le hM γ.position γ'.position

end NearCritical.Section10.NestLayout
