module

public import NearCritical.Section10DistinctArrivalOccupation
public import NearCritical.Section10TwoSoloReadout
public import NearCritical.Section10DisjointArrivalSuffix
public import NearCritical.Section10ArrivalTubeEntry

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
        (Λ.view G.1 (routeLab M γ.position j) z))))
  (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- At a common site with distinct arrival labels, charge the two
prescribed occupations to their respective H1 rows in chronological
order, then carry both occupations to the synchronized prefix. -/
theorem firstGood_distinct_arrival_pair_mass_le
    (hρ : 0 < ρ) (hM : 1 ≤ M)
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d) (x : Λ.X × Λ.X)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (z : RSite D) (hz : z ∈ routeSites M γ.position) (hz' : z ∈ routeSites M γ'.position)
    (j : ℕ) (C C' : Finset (Vertex d)) {A : ℝ} (hA : 0 ≤ A) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let a := routeArrivalRank γ.position z
    let b := routeArrivalRank γ'.position z
    let ℓ := routeLab M γ.position a
    let ℓ' := routeLab M γ'.position b
    let S := jointRoutePrefix M γ.position γ'.position j
    let μ := (percolation d p).prod (percolation d q)
    a < j → b < j → ℓ ≠ ℓ' →
    (0 < a ∧ a+1 < 2*M ∧ ℓ.target ≠ ℓ.site) →
    (0 < b ∧ b+1 < 2*M ∧ ℓ'.target ≠ ℓ'.site) →
    (∀ u, Λ.moveCtx G ℓ u → (∫ w, ∑ y : Λ.X, if C ∈ y.1.val then K γ a u y w else 0 ∂μ) ≤ A) →
    (∀ u, Λ.moveCtx G ℓ' u → (∫ w, ∑ y : Λ.X, if C' ∈ y.1.val then K γ' b u y w else 0 ∂μ) ≤ A) →
    markedPrefixMass p q (K γ) (K γ') S 0 0 x
      (fun h _ => if ∃ y, mergedArrivalStates? S a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
        then 1 else 0) / ρ ^ sharedCount S ≤ A * A := by
  intro G K a b ℓ ℓ' S μ ha hb hne hmove hmove' hrow hrow'
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
  let F (t : List PairMove) (h : NestTrace (Λ.X × Λ.X) t.length)
      (_ : Configuration d × Configuration d) :=
    if ∃ y, mergedArrivalStates? t a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
    then (1:ℝ) else 0
  have hFresh : PairFresh (B γ) (B γ') S 0 0 (Λ.S₀ G.1) :=
    Rule.route_pair_fresh hM γ γ' G j j 0 0
  rcases distinct_arrivals_schedule_split hM γ.position γ'.position hz hz' j ha hb hne with
    ⟨s,gap,tail,hseg,hcl,hcr⟩ | ⟨s,gap,tail,hseg,hcr,hcl⟩
  · let r := s ++ [PairMove.left]
    let u := r ++ gap
    let v := u ++ [PairMove.right]
    change leftCount s = a at hcl
    change rightCount u = b at hcr
    have he : S = v ++ tail := hseg.trans (List.append_assoc u [PairMove.right] tail).symm
    have hf : PairFresh (B γ) (B γ') (v ++ tail) 0 0 (Λ.S₀ G.1) := he ▸ hFresh
    have hv : PairFresh (B γ) (B γ') v 0 0 (Λ.S₀ G.1) :=
      PairFresh.prefix_of_append (B γ) (B γ') v tail 0 0 (Λ.S₀ G.1) hf
    have hfirst : Λ.SoloArrivalH1 p q G K γ γ' s .left C A := by
      unfold SoloArrivalH1
      constructor
      · intro _
        simpa only [hcl] using And.intro hmove hrow
      · intro h
        cases h
    have hsecond : Λ.SoloArrivalH1 p q G K γ γ' u .right C' A := by
      unfold SoloArrivalH1
      constructor
      · intro h
        cases h
      · intro _
        simpa only [hcr] using And.intro hmove' hrow'
    have hsolo := Λ.firstGood_two_solo_arrival_mass_le p q ρ κ hκ hρ hs hsite γ γ' z₀
      hbox hpre hcount s gap .left .right (by intro h; cases h) (by intro h; cases h) x C C' hA hA hv hfirst hsecond
    have ha' : a < leftCount v := by
      change a < leftCount (((s ++ [PairMove.left]) ++ gap) ++ [PairMove.right])
      simp only [leftCount_append,leftCount]
      change leftCount s = a at hcl
      try simp only [u,r,leftCount_append,leftCount] at hcl
      omega
    have hb' : b < rightCount v := by
      change b < rightCount (((s ++ [PairMove.left]) ++ gap) ++ [PairMove.right])
      simp only [rightCount_append,rightCount]
      change rightCount u = b at hcr
      try simp only [u,r,rightCount_append,rightCount] at hcr
      omega
    have hcarry := Rule.arrival_pair_mass_suffix_le hρ γ γ' G x v tail a b ha' hb'
      (fun y => C ∈ y.1.1.val ∧ C' ∈ y.2.1.val) hf
    rw [← he] at hcarry
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount S) ?_)).trans (hcarry.trans ?_)
    · apply markedPrefixMass_congr_of_nonzero
      intro h w _
      dsimp only
      by_cases hw : ∃ y, mergedArrivalStates? S a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
      · simp only [if_pos hw]
      · simp only [if_neg hw]
    let past (h : NestTrace (Λ.X × Λ.X) v.length) :=
      ((mergedTraceAppend (Λ.X × Λ.X) u [PairMove.right]).symm h).1
    let old (h : NestTrace (Λ.X × Λ.X) v.length) :=
      ((mergedTraceAppend (Λ.X × Λ.X) r gap).symm (past h)).1
    have hObs : F v = fun h _ =>
        if (∃ y, soloArrivalState? s .left (old h) = some y ∧ C ∈ y.1.val) ∧
           (∃ y, soloArrivalState? u .right h = some y ∧ C' ∈ y.1.val)
        then 1 else 0 := by
      funext h w
      have ht := mergedArrivalStates?_left_then_right s gap h
      change mergedArrivalStates? v (leftCount s) (rightCount u) h =
        (soloArrivalState? s .left (old h)).bind
          (fun y => (soloArrivalState? u .right h).map (y,·)) at ht
      rw [hcl,hcr] at ht
      unfold F
      rw [ht]
      cases hleft : soloArrivalState? s .left (old h) <;>
        cases hright : soloArrivalState? u .right h <;>
        simp [hleft,hright]
    have hV : markedPrefixMass p q (K γ) (K γ') v 0 0 x (F v) / ρ ^ sharedCount v ≤ A*A := by
      rw [hObs]
      exact hsolo
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount v) ?_)).trans hV
    apply markedPrefixMass_congr_of_nonzero
    intro h w _
    dsimp only [F]
    by_cases hw : ∃ y, mergedArrivalStates? v a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
    · simp only [if_pos hw]
    · simp only [if_neg hw]
  · let r := s ++ [PairMove.right]
    let u := r ++ gap
    let v := u ++ [PairMove.left]
    change leftCount u = a at hcl
    change rightCount s = b at hcr
    have he : S = v ++ tail := hseg.trans (List.append_assoc u [PairMove.left] tail).symm
    have hf : PairFresh (B γ) (B γ') (v ++ tail) 0 0 (Λ.S₀ G.1) := he ▸ hFresh
    have hv : PairFresh (B γ) (B γ') v 0 0 (Λ.S₀ G.1) :=
      PairFresh.prefix_of_append (B γ) (B γ') v tail 0 0 (Λ.S₀ G.1) hf
    have hfirst : Λ.SoloArrivalH1 p q G K γ γ' s .right C' A := by
      unfold SoloArrivalH1
      constructor
      · intro h
        cases h
      · intro _
        simpa only [hcr] using And.intro hmove' hrow'
    have hsecond : Λ.SoloArrivalH1 p q G K γ γ' u .left C A := by
      unfold SoloArrivalH1
      constructor
      · intro _
        simpa only [hcl] using And.intro hmove hrow
      · intro h
        cases h
    have hsolo := Λ.firstGood_two_solo_arrival_mass_le p q ρ κ hκ hρ hs hsite γ γ' z₀
      hbox hpre hcount s gap .right .left (by intro h; cases h) (by intro h; cases h) x C' C hA hA hv hfirst hsecond
    have ha' : a < leftCount v := by
      change a < leftCount (((s ++ [PairMove.right]) ++ gap) ++ [PairMove.left])
      simp only [leftCount_append,leftCount]
      change leftCount u = a at hcl
      try simp only [u,r,leftCount_append,leftCount] at hcl
      omega
    have hb' : b < rightCount v := by
      change b < rightCount (((s ++ [PairMove.right]) ++ gap) ++ [PairMove.left])
      simp only [rightCount_append,rightCount]
      change rightCount s = b at hcr
      try simp only [u,r,rightCount_append,rightCount] at hcr
      omega
    have hcarry := Rule.arrival_pair_mass_suffix_le hρ γ γ' G x v tail a b ha' hb'
      (fun y => C ∈ y.1.1.val ∧ C' ∈ y.2.1.val) hf
    rw [← he] at hcarry
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount S) ?_)).trans (hcarry.trans ?_)
    · apply markedPrefixMass_congr_of_nonzero
      intro h w _
      dsimp only
      by_cases hw : ∃ y, mergedArrivalStates? S a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
      · simp only [if_pos hw]
      · simp only [if_neg hw]
    let past (h : NestTrace (Λ.X × Λ.X) v.length) :=
      ((mergedTraceAppend (Λ.X × Λ.X) u [PairMove.left]).symm h).1
    let old (h : NestTrace (Λ.X × Λ.X) v.length) :=
      ((mergedTraceAppend (Λ.X × Λ.X) r gap).symm (past h)).1
    have hObs : F v = fun h _ =>
        if (∃ y, soloArrivalState? s .right (old h) = some y ∧ C' ∈ y.1.val) ∧
           (∃ y, soloArrivalState? u .left h = some y ∧ C ∈ y.1.val)
        then 1 else 0 := by
      funext h w
      have ht := mergedArrivalStates?_right_then_left s gap h
      change mergedArrivalStates? v (leftCount u) (rightCount s) h =
        (soloArrivalState? u .left h).bind
          (fun y => (soloArrivalState? s .right (old h)).map (y,·)) at ht
      rw [hcl,hcr] at ht
      unfold F
      rw [ht]
      cases hleft : soloArrivalState? u .left h <;>
        cases hright : soloArrivalState? s .right (old h) <;>
        simp [hleft,hright, and_comm]
    have hV : markedPrefixMass p q (K γ) (K γ') v 0 0 x (F v) / ρ ^ sharedCount v ≤ A*A := by
      rw [hObs]
      exact hsolo
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount v) ?_)).trans hV
    apply markedPrefixMass_congr_of_nonzero
    intro h w _
    dsimp only [F]
    by_cases hw : ∃ y, mergedArrivalStates? v a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
    · simp only [if_pos hw]
    · simp only [if_neg hw]

end NearCritical.Section10.NestLayout
