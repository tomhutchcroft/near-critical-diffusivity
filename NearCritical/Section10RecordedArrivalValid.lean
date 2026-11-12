module

public import NearCritical.Section10FrozenRevealHistory
public import NearCritical.Section10HistoryTubeMass

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- A transition invariant holds at every recorded state of a nonzero
route history. -/
theorem routeTraceGet?_valid_of_nonzero {Ω X : Type*}
    (K : ℕ → X → X → Ω → ℝ) (z : Ω)
    (V : ℕ → X → Prop)
    (hstep : ∀ i x y, V i x → K i x y z ≠ 0 → V (i+1) y)
    (n t : ℕ) (x : X) (h : NestTrace X n) (j : ℕ) (y : X)
    (hV : V t x) (hw : routeTraceMass K z n t x h ≠ 0)
    (hy : routeTraceGet? n h j = some y) : V (t+j+1) y := by
  induction n generalizing t x j with
  | zero => simp [routeTraceGet?] at hy
  | succ n ih =>
    change K t x h.1 z * routeTraceMass K z n (t+1) h.1 h.2 ≠ 0 at hw
    have hv := hstep t x h.1 hV (left_ne_zero_of_mul hw)
    cases j with
    | zero =>
      have he : h.1 = y := Option.some.inj hy
      simpa only [Nat.add_zero,he] using hv
    | succ j =>
      have hv' := ih (t+1) h.1 h.2 j hv (right_ne_zero_of_mul hw) hy
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 j] using hv'

namespace NestLayout

set_option maxHeartbeats 400000 in
/-- At a frozen reveal, a recorded arrival in any nonzero merged history
has size (k) and consists of typical clusters of its arrival site. -/
theorem firstGood_recorded_arrivals_valid {D d M : ℕ} (Λ : NestLayout D d)
    [LinearOrder (Finset (Vertex d))] (p q : unitInterval) (ρ κ : ℝ)
    (hκ : 0 < κ) (hρ : 0 < ρ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (z₀ z : Configuration d × Configuration d)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      (routeLab M δ.position j).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position j).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s : List PairMove) (x : Λ.X × Λ.X) (h : NestTrace (Λ.X × Λ.X) s.length) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let V (δ : SourceRoute D M) (j : ℕ) (u : Λ.X) :=
      j+1 < 2*M → u.1.val.card = Λ.k ∧
        u.1.val ⊆ Λ.fam G (routeLab M δ.position (j+1)).site
    Disjoint (Λ.S₀ G.1) (mergedTraceBlocks (B γ) (B γ') s 0 0) →
    mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0 →
    (∀ j u, routeTraceGet? _ (mergedRouteTraces s h).1 j = some u → V γ j u) ∧
    (∀ j u, routeTraceGet? _ (mergedRouteTraces s h).2 j = some u → V γ' j u) := by
  intro G B K V hd hw
  let T := mergedTraceBlocks (B γ) (B γ') s 0 0
  let w := gluePair G.2 (T.restrict (layerVal z))
  obtain ⟨hG,hwz⟩ := Λ.firstGood_glue_fresh_reveal z₀ z T hd
  have hLocal (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (K δ j u v) :=
    stepKernel_isLocal _ _ _ _ v
  obtain ⟨f,hf⟩ := mergedTraceMass_isLocal (B γ) (B γ') (K γ) (K γ')
    (hLocal γ) (hLocal γ') s 0 0 x h
  have he : T.restrict (layerVal w) = T.restrict (layerVal z) := funext fun e => hwz e.val e.property
  have hm : mergedTraceMass (K γ) (K γ') w s 0 0 x h =
      mergedTraceMass (K γ) (K γ') z s 0 0 x h :=
    (hf w).trans ((congrArg f he).trans (hf z).symm)
  have hp : mergedTraceMass (K γ) (K γ') w s 0 0 x h ≠ 0 := hm ▸ hw
  obtain ⟨hpL,hpR⟩ := mergedRouteTraces_mass_ne_zero (K γ) (K γ') w s 0 0 x h hp
  let U (δ : SourceRoute D M) j (u : Λ.X) := 0 < j → j < 2*M →
    u.1.val.card = Λ.k ∧ u.1.val ⊆ Λ.fam G (routeLab M δ.position j).site
  have hstep (δ : SourceRoute D M) (hδ : δ ∈ ({γ,γ'} : Finset (SourceRoute D M)))
      (j : ℕ) (u v : Λ.X) (hu : U δ j u) (hv : K δ j u v w ≠ 0) :
      U δ (j+1) v := by
    intro _ hj
    have hprew (i : ℕ) (hi : i < 2*M) :
        IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) w.1 := by
      apply (Λ.goodCube_iff w (hbox δ hδ i hi)).mp
      rw [hG]
      exact (Λ.goodCube_iff z₀ (hbox δ hδ i hi)).mpr (hpre δ hδ i hi)
    have hk₀ : 0 ≤ K δ j u v w :=
      stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G j u)) v w
    have hinput (hj₀ : 1 ≤ j) : u.1.val.card = Λ.k ∧
        u.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ w) (routeLab M δ.position j).site := by
      rw [hG]
      exact hu hj₀ (by omega)
    have hpos : 0 < (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
        δ (refineReveal Λ.ρ₀ Λ.S₀ w) j u v w := by
      rw [hG]
      exact lt_of_le_of_ne hk₀ hv.symm
    have hnext := Λ.firstGood_route_next_valid δ w p q ρ κ hκ hs hsite
      (hbox δ hδ) hprew hcount j hj u v hinput hpos
    rwa [hG] at hnext
  constructor
  · intro j u hu hj
    have hV := routeTraceGet?_valid_of_nonzero (K γ) w (U γ) (hstep γ (by simp))
      _ 0 x.1 (mergedRouteTraces s h).1 j u (fun h₀ => (Nat.lt_irrefl _ h₀).elim) hpL hu
    simp only [U, Nat.zero_add] at hV
    exact hV (Nat.zero_lt_succ _) hj
  · intro j u hu hj
    have hV := routeTraceGet?_valid_of_nonzero (K γ') w (U γ') (hstep γ' (by simp))
      _ 0 x.2 (mergedRouteTraces s h).2 j u (fun h₀ => (Nat.lt_irrefl _ h₀).elim) hpR hu
    simp only [U, Nat.zero_add] at hV
    exact hV (Nat.zero_lt_succ _) hj

end NestLayout
end NearCritical.Section10
