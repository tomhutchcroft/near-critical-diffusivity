module

public import NearCritical.Section10HistoryMarkSigns
public import NearCritical.Section10FrozenRevealHistory

/-! Exact equality of weighted physical tube marks in the two
representations of a frozen route history. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

/-- In a nonzero joint history both separate route weights are nonzero. -/
theorem mergedRouteTraces_mass_ne_zero {Ω X Y : Type*}
    (K : ℕ → X → X → Ω → ℝ) (K' : ℕ → Y → Y → Ω → ℝ)
    (z : Ω) (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (h : NestTrace (X × Y) s.length)
    (hm : mergedTraceMass K K' z s t t' x h ≠ 0) :
    routeTraceMass K z (leftCount s) t x.1 (mergedRouteTraces s h).1 ≠ 0 ∧
      routeTraceMass K' z (rightCount s) t' x.2 (mergedRouteTraces s h).2 ≠ 0 := by
  have he := mergedTraceMass_interleave K K' z s t t' x (mergedRouteTraces s h).1
    (mergedRouteTraces s h).2
  rw [interleave_mergedRouteTraces_of_nonzero K K' z s t t' x h hm] at he
  rw [he] at hm
  exact ⟨left_ne_zero_of_mul hm, right_ne_zero_of_mul hm⟩

/-- The row between two consecutive recorded states of a nonzero route
history has nonzero weight. This can be used to transport a nest through
a stay even when the other route advances on its own clock. -/
theorem routeTraceMass_adjacent_ne_zero {Ω X : Type*} (K : ℕ → X → X → Ω → ℝ)
    (z : Ω) (n t : ℕ) (x : X) (h : NestTrace X n) (j : ℕ) (u v : X)
    (hu : routeTraceGet? n h j = some u) (hv : routeTraceGet? n h (j+1) = some v)
    (hm : routeTraceMass K z n t x h ≠ 0) :
    K (t+j+1) u v z ≠ 0 := by
  induction n generalizing t x j with
  | zero => simp [routeTraceGet?] at hu
  | succ n ih =>
    have htail : routeTraceMass K z n (t+1) h.1 h.2 ≠ 0 :=
      right_ne_zero_of_mul (show K t x h.1 z * routeTraceMass K z n (t+1) h.1 h.2 ≠ 0 from hm)
    cases j with
    | zero =>
      have he : h.1 = u := Option.some.inj hu
      change routeTraceGet? n h.2 0 = some v at hv
      cases n with
      | zero => simp [routeTraceGet?] at hv
      | succ n =>
        have he' : h.2.1 = v := Option.some.inj hv
        have hrow : K (t+1) h.1 h.2.1 z ≠ 0 :=
          left_ne_zero_of_mul (show K (t+1) h.1 h.2.1 z *
            routeTraceMass K z n (t+1+1) h.2.1 h.2.2 ≠ 0 from htail)
        simpa only [he, he', Nat.add_zero] using hrow
    | succ j =>
      change routeTraceGet? n h.2 j = some u at hu
      change routeTraceGet? n h.2 (j+1) = some v at hv
      have he : t+1+j+1 = t+(j+1)+1 := by omega
      rw [← he]
      exact ih (t+1) h.1 h.2 j hu hv htail

end NearCritical.Section10

namespace NearCritical.Section10.NestLayout

open scoped Classical

theorem historyTubeMark_used_iff_pending_of_lt {D d : ℕ} (Λ : NestLayout D d)
    (G : Λ.Φ) (ℓ : RouteLabel D) (active active' : ℕ → Bool)
    (n n' j j' : ℕ) (a b : Bool) (h : NestTrace Λ.X n) (h' : NestTrace Λ.X n')
    (hj : j+1 < n) (hj' : j'+1 < n') (ha : active (j+1) = true) (hb : active' (j'+1) = true)
    (z : Configuration d × Configuration d) :
    Λ.historyTubeMark G ℓ true n n' j j'
      (eraseInitialUsedSign n (usedMaskedTrace active n 0 a h))
      (eraseInitialUsedSign n' (usedMaskedTrace active' n' 0 b h')) z ↔
    Λ.historyTubeMark G ℓ false n n' j j' h h' z := by
  obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp ((routeTraceGet?_isSome n h j).mpr (by omega))
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp ((routeTraceGet?_isSome n h (j+1)).mpr hj)
  obtain ⟨u',hu'⟩ := Option.isSome_iff_exists.mp ((routeTraceGet?_isSome n' h' j').mpr (by omega))
  obtain ⟨v',hv'⟩ := Option.isSome_iff_exists.mp ((routeTraceGet?_isSome n' h' (j'+1)).mpr hj')
  exact Λ.historyTubeMark_used_iff_pending G ℓ active active' n n' j j' a b h h'
    u v u' v' hu hv hu' hv' ha hb z

theorem historyTubeMark_used_erase {D d : ℕ} (Λ : NestLayout D d)
    (G : Λ.Φ) (ℓ : RouteLabel D) (n n' j j' : ℕ)
    (h : NestTrace Λ.X n) (h' : NestTrace Λ.X n') (z : Configuration d × Configuration d) :
    Λ.historyTubeMark G ℓ true n n' j j' (eraseInitialUsedSign n h) (eraseInitialUsedSign n' h') z =
      Λ.historyTubeMark G ℓ true n n' j j' h h' z := by
  simp only [historyTubeMark, if_true, routeTraceGet?_eraseInitialUsedSign_nest,
    routeTraceGet?_eraseInitialUsedSign_succ]

/-- A weighted combination of physical tube marks can be evaluated
using the signs on the moves themselves. The result holds with the
reveal frozen and on every sample of the fresh bits. -/
theorem firstGood_frozen_tube_marks_eq_used
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (z₀ z : Configuration d × Configuration d) (hM : 1 ≤ M)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      (routeLab M δ.position j).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position j).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s : List PairMove) (x x' : Λ.X) (b b' : Bool)
    {I : Type*} (ℓ : I → RouteLabel D) (j j' : I → ℕ) (g : (I → Prop) → ℝ)
    (hj : ∀ i, j i+1 < leftCount s) (hj' : ∀ i, j' i+1 < rightCount s)
    (ha : ∀ i, routeSignDraw γ (j i+1) = true) (ha' : ∀ i, routeSignDraw γ' (j' i+1) = true) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let L (δ : SourceRoute D M) := usedMaskedKernel (routeSignDraw δ)
      (Λ.firstGoodMaskBase p q ρ κ hκ hs hsite δ G (routeSignDraw δ))
    let F used (h : NestTrace Λ.X (leftCount s)) (h' : NestTrace Λ.X (rightCount s)) :=
      g (fun i => Λ.historyTubeMark G (ℓ i) used (leftCount s) (rightCount s) (j i) (j' i) h h' z)
    Disjoint (Λ.S₀ G.1) (mergedTraceBlocks (B γ) (B γ') s 0 0) →
    (∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F false (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 *
        mergedTraceMass (K γ) (K γ') z s 0 0 (x,x') h) =
    ∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F true (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 *
        mergedTraceMass (L γ) (L γ') z s 0 0 ((x.1,b),(x'.1,b')) h := by
  intro G B K L F hd
  let n := leftCount s
  let n' := rightCount s
  let U (δ : SourceRoute D M) k a (h : NestTrace Λ.X k) :=
    eraseInitialUsedSign k (usedMaskedTrace (routeSignDraw δ) k 0 a h)
  have hused := Λ.firstGood_frozen_merged_marked_sum_fixedStart p q ρ κ hκ hs hsite γ γ'
    z₀ z hM hbox hpre hcount s x x' b b' (F true) hd
  calc
    _ = ∑ h : NestTrace (Λ.X × Λ.X) s.length,
        F true (U γ n x.2 (mergedRouteTraces s h).1)
          (U γ' n' x'.2 (mergedRouteTraces s h).2) *
          mergedTraceMass (K γ) (K γ') z s 0 0 (x,x') h := by
      refine Finset.sum_congr rfl fun h _ => ?_
      congr 1
      apply congrArg g
      funext i
      exact propext (Λ.historyTubeMark_used_iff_pending_of_lt G (ℓ i)
        (routeSignDraw γ) (routeSignDraw γ') n n' (j i) (j' i) x.2 x'.2
        (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 (hj i) (hj' i) (ha i) (ha' i) z).symm
    _ = ∑ h : NestTrace (Λ.X × Λ.X) s.length,
        F true (eraseInitialUsedSign n (mergedRouteTraces s h).1)
          (eraseInitialUsedSign n' (mergedRouteTraces s h).2) *
          mergedTraceMass (L γ) (L γ') z s 0 0 ((x.1,b),(x'.1,b')) h := hused
    _ = _ := by
      refine Finset.sum_congr rfl fun h _ => ?_
      congr 1
      apply congrArg g
      funext i
      exact Λ.historyTubeMark_used_erase G (ℓ i) n n' (j i) (j' i)
        (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 z

end NearCritical.Section10.NestLayout
