module

public import NearCritical.Section10HistoryTubeMass
public import NearCritical.Section10ArrivalPairGeometry
public import NearCritical.Section10FirstGoodInitialLaw
public import NearCritical.Section10MergedArrival

/-! At any interior local clock, the incoming nest in a nonzero
history is exactly the one recorded on arrival at the site. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open scoped Classical

theorem firstGood_routeTraceLast_eq_arrival
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ : SourceRoute D M) (G : Λ.Φ) (z : Configuration d × Configuration d)
    (n : ℕ) (hn₀ : 0 < n) (hn : n < 2*M) (x : Λ.X) (h : NestTrace Λ.X n) :
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel γ G
    let a := routeArrivalRank γ.position (routeLab M γ.position n).site
    routeTraceMass K z n 0 x h ≠ 0 →
    routeTraceGet? n h a = some (routeTraceLast n x h) := by
  intro K a hm
  have hl := routeTraceGet?_last n x h hn₀
  rcases routeLab_source_arrival_or_stay γ.position hn₀ hn with he | ⟨he,h3,hs₀,hstay⟩
  · change a = n-1 at he
    rwa [he]
  · change a = n-2 at he
    have han : a < n := by omega
    obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp ((routeTraceGet?_isSome n h a).mpr han)
    have hnext : a+1 = n-1 := by omega
    have hv : routeTraceGet? n h (a+1) = some (routeTraceLast n x h) := by rwa [hnext]
    have hk := routeTraceMass_adjacent_ne_zero K z n 0 x h a u (routeTraceLast n x h) hu hv hm
    rw [Nat.zero_add, hnext] at hk
    have hrow : K (n-1) u (routeTraceLast n x h) z =
        if routeTraceLast n x h = u then (1:ℝ) else 0 :=
      Λ.firstGood_stay_kernel_identity p q ρ κ hκ hs hsite γ G (n-1) u
        (routeTraceLast n x h) z hs₀ hstay
    have hu' : routeTraceLast n x h = u := by
      by_contra hne
      exact hk (hrow.trans (if_neg hne))
    exact hu.trans (congrArg some hu'.symm)

/-- The actual incoming nests at both local clocks can be read from
their separate arrival rows in the merged prefix. -/
theorem firstGood_mergedTraceLast_eq_arrivals
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (z : Configuration d × Configuration d)
    (s : List PairMove) (x : Λ.X × Λ.X) (h : NestTrace (Λ.X × Λ.X) s.length)
    (ha₀ : 0 < leftCount s) (ha : leftCount s < 2*M)
    (hb₀ : 0 < rightCount s) (hb : rightCount s < 2*M) :
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let a := routeArrivalRank γ.position (routeLab M γ.position (leftCount s)).site
    let b := routeArrivalRank γ'.position (routeLab M γ'.position (rightCount s)).site
    mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0 →
    mergedArrivalStates? s a b h = some (mergedTraceLast s x h) := by
  intro K a b hm
  obtain ⟨hl,hr⟩ := mergedRouteTraces_mass_ne_zero (K γ) (K γ') z s 0 0 x h hm
  have he := mergedTraceLast_eq_routeTraceLast (K γ) (K γ') z s 0 0 x h hm
  have hleft := Λ.firstGood_routeTraceLast_eq_arrival p q ρ κ hκ hs hsite γ G z
    (leftCount s) ha₀ ha x.1 (mergedRouteTraces s h).1 hl
  have hright := Λ.firstGood_routeTraceLast_eq_arrival p q ρ κ hκ hs hsite γ' G z
    (rightCount s) hb₀ hb x.2 (mergedRouteTraces s h).2 hr
  dsimp only [mergedArrivalStates?,a,b]
  rw [hleft,hright,he]

end NearCritical.Section10.NestLayout
