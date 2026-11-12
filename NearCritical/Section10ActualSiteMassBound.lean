module

public import NearCritical.Section10ActualTubeMassBound
public import NearCritical.Section10TerminalSiteMass

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- Each common physical site has normalized collision mass of order
`t^(6-d)` on the terminal history. -/
theorem actualLayout_terminal_site_mass_le {D : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
    (hd : 7 ≤ D+1) (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp₀ : 0 < (criticalPoint (D+1) : ℝ)) (hp₁ : (criticalPoint (D+1) : ℝ) < 1)
    (typ : TypicalParameters) (hr : 1 ≤ typ.regularRadius) (hb : 0 ≤ typ.boundaryUpper)
    (hl : 0 < typ.countLower) (hu : 0 ≤ typ.countUpper) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℕ, ∀ (t : ℕ) (ht : 9 ≤ t), T ≤ t →
    ∀ (MOff Mcoal Kdiam M : ℕ), 1 ≤ M →
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    let p := criticalPoint (D+1)
    ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
    ∀ (ρ κ : ℝ) (hκ : 0 < κ), 1 ≤ ρ → ρ ≤ 9/8 →
    ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
      (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
    ∀ (γ γ' : SourceRoute D M) (z : Configuration (D+1) × Configuration (D+1))
      (x x' : Λ.X),
    (∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      (routeLab M δ.position j).site ∈ Λ.siteBox) →
    (∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position j).site) z.1) →
    (k:ℝ) ≤ typ.countLower * (2*(t:ℝ))^(D+1-6) →
    ∀ s ∈ routeSites M γ.position ∩ routeSites M γ'.position,
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let r := jointRoutePrefix M γ.position γ'.position (2*M)
    let a := routeArrivalRank γ.position s
    let b := routeArrivalRank γ'.position s
    markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x')
      (fun h _ => if mergedSiteMark Λ r a b h then 1 else 0) / ρ ^ sharedCount r ≤
        C * (t:ℝ)^(6-((D+1:ℕ):ℝ)) := by
  obtain ⟨Ct,hCt,T,hT⟩ := actualLayout_shared_tube_mass_le hd asymp q₀ hp₀ hp₁ typ hr hb hl hu k hk
  obtain ⟨C₁,hC₁⟩ := actualLayout_firstGood_child_row (by omega) asymp q₀ hp₀ hp₁ typ hb
  obtain ⟨C₂,hC₂⟩ := actualLayout_firstGood_disjoint_child_pair_row (by omega) asymp q₀ hp₀ hp₁ typ hb
  let H₀ := (9/8:ℝ) * (k:ℝ) * max 0 C₁
  let A₂ := (9/8:ℝ) * ((k:ℝ)^2 * max 0 C₂)
  let A₀ := H₀^2 + A₂
  let N₀ := typ.countUpper * (2:ℝ)^(D+1-6)
  let Cr := (k:ℝ)^2 / typ.countLower
  let C := max Cr (Ct + N₀*A₀)
  have hH₀ : 0 ≤ H₀ := mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (le_max_left _ _)
  have hA₂ : 0 ≤ A₂ := mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (le_max_left _ _))
  have hA₀ : 0 ≤ A₀ := add_nonneg (sq_nonneg _) hA₂
  have hN₀ : 0 ≤ N₀ := mul_nonneg hu (pow_nonneg (by norm_num) _)
  refine ⟨C, (div_nonneg (sq_nonneg _) hl.le).trans (le_max_left _ _), T, ?_⟩
  intro t ht htT MOff Mcoal Kdiam M hM Λ p q hq ρ κ hκ hρ hρ' hs hsite γ γ' z x x'
    hbox hpre hcount s hs' G K r a b
  obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hs'
  let ℓ := routeLab M γ.position a
  let ℓ' := routeLab M γ'.position b
  let S := Λ.fam G s
  let v : ℝ := (t:ℝ)^(D+1-6)
  let A := A₀ * v⁻¹^2
  let H := H₀ * v⁻¹
  let E := Ct * v⁻¹
  have hρ₀ := zero_lt_one.trans_le hρ
  have ht₀ : 0 < (t:ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hv : 0 < v := pow_pos ht₀ _
  have hv₀ := (inv_pos.mpr hv).le
  have hexp : (6:ℝ) - ((D+1:ℕ):ℝ) = -((D+1-6:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num <;> ring
  have hscale : (t:ℝ)^(6-((D+1:ℕ):ℝ)) = v⁻¹ := by
    rw [hexp, Real.rpow_neg ht₀.le, Real.rpow_natCast]
  have hscale₂ : (t:ℝ)^(12-2*((D+1:ℕ):ℝ)) = v⁻¹^2 := by
    rw [show (12:ℝ)-2*((D+1:ℕ):ℝ) = (6-((D+1:ℕ):ℝ))*2 by ring,
      Real.rpow_mul ht₀.le, hscale, Real.rpow_two]
  have haM : a < 2*M := (routeArrivalRank_arrives γ.position ha).1
  have ha₁ : a+1 < 2*M := by
    by_cases h : a = 0
    · omega
    · exact (routeLab_hasTube_clock hM γ.position haM (routeArrivalRank_hasTube γ ha (by omega))).2
  have hza : ℓ.target = s := (routeArrivalRank_arrives γ.position ha).2.1
  have hzb : ℓ'.target = s := (routeArrivalRank_arrives γ'.position hb).2.1
  have hgood : Λ.goodCube G s := by
    have he := (routeLab_next_site γ.position ha₁).trans hza
    rw [← he]
    exact (Λ.goodCube_iff z (hbox γ (by simp) (a+1) ha₁)).mpr (hpre γ (by simp) (a+1) ha₁)
  have hLower : typ.countLower*v ≤ (S.card:ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀.le (show (t:ℝ) ≤ 2*(t:ℝ) by linarith) _) hl.le).trans hgood.1
  have hUpper : (S.card:ℝ) ≤ N₀*v := by
    refine hgood.2.trans_eq ?_
    change typ.countUpper * (2*(t:ℝ))^(D+1-6) = N₀*v
    rw [mul_pow]
    simp only [N₀,v,mul_assoc]
  have hHA : H*H ≤ A := by
    change (H₀*v⁻¹)*(H₀*v⁻¹) ≤ A₀*v⁻¹^2
    rw [← sq, mul_pow]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₂) (sq_nonneg _)
  have hchild (δ : SourceRoute D M) (i : ℕ) (B : Finset (Vertex (D+1)))
      (hB : B ∈ Λ.fam G (routeLab M δ.position i).target) (u : Λ.X)
      (hctx : Λ.moveCtx G (routeLab M δ.position i) u) :
      (∫ w, ∑ y : Λ.X, if B ∈ y.1.val then K δ i u y w else 0
        ∂((percolation (D+1) p).prod (percolation (D+1) q))) ≤ H := by
    have hh := hC₁ t ht k hk MOff Mcoal Kdiam M q hq ρ κ hκ hρ₀ hs hsite G δ i u B hctx hB
    refine hh.trans ?_
    rw [hscale]
    calc
      _ ≤ ρ * (k:ℝ) * (max 0 C₁ * v⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_right _ _) hv₀)
          (mul_nonneg hρ₀.le (Nat.cast_nonneg _))
      _ ≤ (9/8:ℝ) * (k:ℝ) * (max 0 C₁ * v⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ' (Nat.cast_nonneg _))
          (mul_nonneg (le_max_left _ _) hv₀)
      _ = H := by dsimp only [H,H₀]; ring
  refine (Λ.firstGood_terminal_site_mass_le p q ρ κ hκ hs hsite hρ hM γ γ' z x x' hbox hpre hcount s ha hb
    (mul_nonneg hA₀ (sq_nonneg _)) (mul_nonneg hH₀ hv₀) (mul_nonneg hCt hv₀) hHA
    (fun B hB => hchild γ a B (by rwa [hza]))
    (fun B hB => hchild γ' b B (by rwa [hzb])) ?_ ?_).trans ?_
  · intro hEq B hB u u' hctx hctx'
    have hh := hC₂ t ht k hk MOff Mcoal Kdiam M q hq ρ κ hκ hρ₀ hs hsite
      G γ γ' a b u u' B B hEq.symm hctx (hEq.symm ▸ hctx')
      (by rwa [hza]) (by rwa [hza])
    simp only [ite_mul,zero_mul,one_mul]
    refine hh.trans ?_
    rw [hscale₂]
    have hA₂' : ρ * ((k:ℝ)^2 * (C₂ * v⁻¹^2)) ≤ A₂ * v⁻¹^2 := by
      calc
        _ ≤ ρ * ((k:ℝ)^2 * (max 0 C₂ * v⁻¹^2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) (sq_nonneg _))
            hρ₀.le
        _ ≤ (9/8:ℝ) * ((k:ℝ)^2 * (max 0 C₂ * v⁻¹^2)) :=
          mul_le_mul_of_nonneg_right hρ' (mul_nonneg (sq_nonneg _) (mul_nonneg (le_max_left _ _) (sq_nonneg _)))
        _ = _ := by dsimp only [A₂]; ring
    rw [sq,mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hA₂'.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg H₀)) (sq_nonneg _))) hρ₀.le
  · intro hEq hTube
    have hab : a = b := by
      have hh := congrArg RouteLabel.rank hEq
      change (routeLab M γ.position a).rank = (routeLab M γ'.position b).rank at hh
      rwa [rank_routeLab hM,rank_routeLab hM] at hh
    have hh := hT t ht htT MOff Mcoal Kdiam M hM q hq ρ κ hκ hρ hρ' hs hsite γ γ' z x x'
      hbox hpre hcount a haM (hEq.trans (congrArg (routeLab M γ'.position) hab.symm)) hTube
    simpa only [hscale,E] using hh
  · rw [hscale]
    apply max_le
    · calc
        _ ≤ (k:ℝ)^2 / (typ.countLower*v) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hl hv) hLower
        _ = Cr*v⁻¹ := by
          dsimp only [Cr]
          field_simp [hl.ne',hv.ne'] <;> ring
        _ ≤ C*v⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) hv₀
    · have he : (N₀*v)*A = (N₀*A₀)*v⁻¹ := by
        change (N₀*v)*(A₀*v⁻¹^2) = _
        calc
          _ = ((N₀*A₀)*v⁻¹)*(v*v⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hv.ne',mul_one]
      calc
        _ ≤ E + (N₀*v)*A := add_le_add le_rfl (mul_le_mul_of_nonneg_right hUpper (mul_nonneg hA₀ (sq_nonneg _)))
        _ = (Ct + N₀*A₀)*v⁻¹ := by rw [he]; dsimp only [E]; ring
        _ ≤ C*v⁻¹ := mul_le_mul_of_nonneg_right (le_max_right _ _) hv₀

end NearCritical.Section10
