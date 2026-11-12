module

public import NearCritical.Section10SharedTubeMassBound
public import NearCritical.Section10ActualBridgeRow
public import NearCritical.Section10ActualOppositeBridges
public import NearCritical.Section10FirstGoodOccupationRow
public import NearCritical.Section10FirstGoodDisjointRow

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- For fixed typicality constants and nest size, each shared physical
tube has normalized mark mass of order `t^(6-d)`, uniformly in the
route lengths and the realized pre-good cubes. -/
theorem actualLayout_shared_tube_mass_le {D : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
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
    ∀ j < 2*M, routeLab M γ.position j = routeLab M γ'.position j →
    HasTube M (routeLab M γ.position j) →
    Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ'
      (refineReveal Λ.ρ₀ Λ.S₀ z) (x,x') j ≤ C * (t:ℝ)^(6-((D+1:ℕ):ℝ)) := by
  obtain ⟨C₁,hC₁⟩ := actualLayout_firstGood_child_row (by omega) asymp q₀ hp₀ hp₁ typ hb
  obtain ⟨C₂,hC₂⟩ := actualLayout_firstGood_disjoint_child_pair_row (by omega) asymp q₀ hp₀ hp₁ typ hb
  obtain ⟨K,hK⟩ := actualLayout_bridge_row_uniform hd asymp q₀ hp₀ hp₁ typ hr hb
  obtain ⟨T,hT⟩ := actualLayout_oppositeBridge_small hd asymp q₀ hp₀ hp₁ typ hb k hk
  let K₀ := max 0 K
  let H₀ := (9/8:ℝ) * (k:ℝ) * max 0 C₁
  let A₂ := (9/8:ℝ) * ((k:ℝ)^2 * max 0 C₂)
  let A₀ := ((k:ℝ)/typ.countLower)^2 + H₀^2 + A₂
  let N₀ := typ.countUpper * (2:ℝ)^(D+1-6)
  let C := 3 * ((9/8:ℝ) * (N₀ * (A₀ * (1+4*K₀))))
  have hK₀ : 0 ≤ K₀ := le_max_left _ _
  have hH₀ : 0 ≤ H₀ := mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (le_max_left _ _)
  have hA₂ : 0 ≤ A₂ := mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (le_max_left _ _))
  have hA₀ : 0 ≤ A₀ := add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hA₂
  have hN₀ : 0 ≤ N₀ := mul_nonneg hu (pow_nonneg (by norm_num) _)
  have hK₁ : 0 ≤ 1+4*K₀ := by linarith
  refine ⟨C, mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
    (mul_nonneg hN₀ (mul_nonneg hA₀ hK₁))), T, ?_⟩
  intro t ht htT MOff Mcoal Kdiam M hM Λ p q hq ρ κ hκ hρ hρ' hs hsite γ γ' z x x' hbox hpre hcount
    j hj hEq hTube
  let G := refineReveal Λ.ρ₀ Λ.S₀ z
  let L (δ : SourceRoute D M) i := routeLab M δ.position i
  let μ := (percolation (D+1) p).prod (percolation (D+1) q)
  let F := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
  let v : ℝ := (t:ℝ)^(D+1-6)
  let A := A₀ * v⁻¹^2
  let H := H₀ * v⁻¹
  let N := N₀ * v
  have ht₀ : 0 < (t:ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hv : 0 < v := pow_pos ht₀ _
  have hv₀ := (inv_pos.mpr hv).le
  have hρ₀ := zero_lt_one.trans_le hρ
  have hexp : (6:ℝ) - ((D+1:ℕ):ℝ) = -((D+1-6:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num <;> ring
  have hscale : (t:ℝ)^(6-((D+1:ℕ):ℝ)) = v⁻¹ := by
    rw [hexp, Real.rpow_neg ht₀.le, Real.rpow_natCast]
  have hscale₂ : (t:ℝ)^(12-2*((D+1:ℕ):ℝ)) = v⁻¹^2 := by
    rw [show (12:ℝ)-2*((D+1:ℕ):ℝ) = (6-((D+1:ℕ):ℝ))*2 by ring,
      Real.rpow_mul ht₀.le, hscale, Real.rpow_two]
  have hgood (δ : SourceRoute D M) (hδ : δ ∈ ({γ,γ'} : Finset (SourceRoute D M))) (i : ℕ) (hi : i < 2*M) :
      Λ.goodCube G (L δ i).site := (Λ.goodCube_iff z (hbox δ hδ i hi)).mpr (hpre δ hδ i hi)
  have hN (i : ℕ) (hi : i < 2*M) : ((Λ.fam G (L γ i).site).card:ℝ) ≤ N := by
    refine (hgood γ (by simp) i hi).2.trans_eq ?_
    change typ.countUpper * (2*(t:ℝ))^(D+1-6) = N₀*v
    rw [mul_pow]
    simp only [N₀,v,mul_assoc]
  have hroot : ((k:ℝ)/(Λ.fam G (L γ 1).site).card)^2 ≤ A := by
    have h1 : 1 < 2*M := by omega
    have hcount₁ : typ.countLower * v ≤ ((Λ.fam G (L γ 1).site).card:ℝ) := by
      refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀.le ?_ _) hl.le)
        (hgood γ (by simp) 1 h1).1
      change (t:ℝ) ≤ 2*(t:ℝ)
      linarith
    have hL : 0 < typ.countLower * v := mul_pos hl hv
    have hdiv : (k:ℝ)/(Λ.fam G (L γ 1).site).card ≤ ((k:ℝ)/typ.countLower)*v⁻¹ := by
      rw [← div_eq_mul_inv, div_div]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hL hcount₁
    calc
      _ ≤ (((k:ℝ)/typ.countLower)*v⁻¹)^2 := pow_le_pow_left₀ (by positivity) hdiv _
      _ = ((k:ℝ)/typ.countLower)^2 * v⁻¹^2 := mul_pow _ _ _
      _ ≤ A := mul_le_mul_of_nonneg_right (by dsimp only [A₀]; linarith [sq_nonneg H₀]) (sq_nonneg _)
  have hHA : H*H ≤ A := by
    change (H₀*v⁻¹)*(H₀*v⁻¹) ≤ A₀*v⁻¹^2
    rw [← sq, mul_pow]
    exact mul_le_mul_of_nonneg_right (by dsimp only [A₀]; linarith [sq_nonneg ((k:ℝ)/typ.countLower)]) (sq_nonneg _)
  refine (Λ.firstGood_shared_tube_mass_le p q ρ κ hκ hs hsite hρ hρ' hM γ γ' z x x'
    hbox hpre hcount (mul_nonneg hA₀ (sq_nonneg _)) (mul_nonneg hH₀ hv₀) hK₀ (mul_nonneg hN₀ hv.le) hHA
    (fun i hi => hN i hi.1) (fun _ => hroot) ?_ ?_ ?_ ?_ j ⟨hj,hEq,hTube⟩).trans ?_
  · intro δ _ i _ B hB u hctx
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
  · intro i hi B hB B' hB' u u' hctx hctx'
    have hh := hC₂ t ht k hk MOff Mcoal Kdiam M q hq ρ κ hκ hρ₀ hs hsite
      G γ γ' i i u u' B B' hi.2.1.symm hctx hctx' hB hB'
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
    rw [sq, mul_assoc]
    have hA₂le : A₂ ≤ A₀ := le_add_of_nonneg_left (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact mul_le_mul_of_nonneg_left
      (hA₂'.trans (mul_le_mul_of_nonneg_right hA₂le (sq_nonneg _))) hρ₀.le
  · intro i hi u u' hctx hctx' e e' hne
    obtain ⟨hstep,_,hsrc,htgt,hcard,hfam,_,hgt,_⟩ := hctx
    obtain ⟨_,_,_,_,hcard',hfam',_,_,_⟩ := hctx'
    exact hT t ht htT MOff Mcoal Kdiam M z (L γ i) hi.2.2 hstep hsrc htgt hgt
      q hq u.1.val u'.1.val e e' hne hfam hfam' hcard hcard'
  · intro i hi B hB e e'
    obtain ⟨hi₀,hi₁⟩ := routeLab_hasTube_clock hM γ.position hi.1 hi.2.2
    have hstep := routeLab_isStep γ.position (show 1 ≤ i by omega) (show i < 2*M-1 by omega)
    have he := routeLab_next_site γ.position hi₁
    have hsrc := hbox γ (by simp) i hi.1
    have htgt : (L γ i).target ∈ Λ.siteBox := by rw [← he]; exact hbox γ (by simp) _ hi₁
    have hgt : Λ.goodCube G (L γ i).target := by rw [← he]; exact hgood γ (by simp) _ hi₁
    exact (hK t ht k hk MOff Mcoal Kdiam M z (L γ i) hi.2.2 hstep hsrc htgt
      (hgood γ (by simp) i hi.1) hgt q hq B hB e e').trans (le_max_right _ _)
  · rw [hscale]
    change 3 * (ρ * ((N₀ * v) * ((A₀ * v⁻¹^2) * (1+4*K₀)))) ≤ C * v⁻¹
    have hv' : v * v⁻¹ = 1 := mul_inv_cancel₀ hv.ne'
    have he : (N₀ * v) * ((A₀ * v⁻¹^2) * (1+4*K₀)) =
        (N₀ * (A₀ * (1+4*K₀))) * v⁻¹ := by
      calc
        _ = ((N₀ * (A₀ * (1+4*K₀))) * v⁻¹) * (v * v⁻¹) := by ring
        _ = _ := by rw [hv',mul_one]
    rw [he]
    calc
      _ ≤ 3 * ((9/8:ℝ) * ((N₀ * (A₀ * (1+4*K₀))) * v⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hρ' (mul_nonneg (mul_nonneg hN₀ (mul_nonneg hA₀ hK₁)) hv₀))
          (by norm_num)
      _ = _ := by dsimp only [C]; ring

end NearCritical.Section10
