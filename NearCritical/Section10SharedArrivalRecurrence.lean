module

public import NearCritical.Section10TubeRecurrenceStep
public import NearCritical.Section10DisjointArrivalSuffix
public import NearCritical.Section10SharedArrivalOccupation
public import NearCritical.Section10DistinctArrivalSchedule

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

/-- Normalized mass of the shared tube at local clock `j` in the
synchronized schedule through its moving row. -/
def firstGood_shared_tube_mass (γ γ' : SourceRoute D M) (G : Λ.Φ) (x : Λ.X × Λ.X)
    (j : ℕ) : ℝ :=
  let s := jointRoutePrefix M γ.position γ'.position (j+1)
  let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
  markedPrefixMass p q (K γ) (K γ') s 0 0 x
    (fun h z => if Λ.mergedTubeMark G (routeLab M γ.position j) false s (j-1) (j-1) h z
      then 1 else 0) / ρ ^ sharedCount s

set_option maxHeartbeats 500000 in
/-- The H2 and persistence terms at a current shared tube are both
charged to the prefix through the earlier shared physical arrival. -/
theorem firstGood_shared_arrival_recurrence_le
    (hρ : 1 ≤ ρ) (hρ' : ρ ≤ 9/8) (hM : 1 ≤ M)
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d) (x x' : Λ.X)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (a j : ℕ) (ha : 0 < a) (haj : a < j) (hj : j+1 < 2*M)
    (hprev : routeLab M γ.position a = routeLab M γ'.position a)
    (hcur : routeLab M γ.position j = routeLab M γ'.position j)
    (hpa : HasTube M (routeLab M γ.position a)) (hpj : HasTube M (routeLab M γ.position j))
    (hArrival : routeArrivalRank γ.position (routeLab M γ.position j).site = a)
    (hArrival' : routeArrivalRank γ'.position (routeLab M γ'.position j).site = a)
    {A K₀ : ℝ} (hA : 0 ≤ A) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let ℓ₀ := routeLab M γ.position a
    let ℓ := routeLab M γ.position j
    let S := Λ.fam G ℓ.site
    let μ := (percolation d p).prod (percolation d q)
    (∀ C ∈ S, ∀ C' ∈ S, ∀ u v : Λ.X, Λ.moveCtx G ℓ₀ u → Λ.moveCtx G ℓ₀ v →
      (∫ z, (if Λ.firstGoodSharedTubeMark G ℓ₀ u.1.val v.1.val u.2 v.2 z then 0 else 1) *
        ((∑ y : Λ.X, if C ∈ y.1.val then K γ a u y z else 0) *
         (∑ y : Λ.X, if C' ∈ y.1.val then K γ' a v y z else 0)) ∂μ) ≤ ρ*A) →
    (∀ u v : Λ.X, Λ.moveCtx G ℓ u → Λ.moveCtx G ℓ v → ∀ e e', e ≠ e' →
      μ.real {z | Λ.firstGoodSharedTubeMark G ℓ u.1.val v.1.val e e' z} ≤ 1/40) →
    (∀ C ∈ S, ∀ e e' : Bool,
      (∑ C' ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {C'} e e' z}) ≤ K₀) →
    Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G (x,x') j ≤
      ρ * ((S.card:ℝ) * (A * (1+4*K₀))) +
        (2/3:ℝ) * Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G (x,x') a := by
  intro G K ℓ₀ ℓ S μ hH2 hrare hrow
  let P := jointRoutePrefix M γ.position γ'.position
  let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  have hf (k : ℕ) : PairFresh (B γ) (B γ') (P k) 0 0 (Λ.S₀ G.1) :=
    Rule.route_pair_fresh hM γ γ' G k k 0 0
  have hPa : P (a+1) = P a ++ [.both] := by rw [show P (a+1) = _ from jointRoutePrefix_succ hM _ _ _, if_pos hprev]
  have hPj : P (j+1) = P j ++ [.both] := by rw [show P (j+1) = _ from jointRoutePrefix_succ hM _ _ _, if_pos hcur]
  obtain ⟨r,hr⟩ := jointRoutePrefix_extends hM γ.position γ'.position (show a+1 ≤ j by omega)
  change P j = P (a+1) ++ r at hr
  obtain ⟨hLa,hRa⟩ := jointRoutePrefix_clocks M γ.position γ'.position a
  obtain ⟨hLas,hRas⟩ := jointRoutePrefix_clocks M γ.position γ'.position (a+1)
  obtain ⟨hLj,hRj⟩ := jointRoutePrefix_clocks M γ.position γ'.position j
  change leftCount (P a) = a at hLa
  change rightCount (P a) = a at hRa
  change leftCount (P j) = j at hLj
  change rightCount (P j) = j at hRj
  have hρ₀ := zero_lt_one.trans_le hρ
  have hfa : PairFresh (B γ) (B γ') (P a ++ [.both]) 0 0 (Λ.S₀ G.1) := hPa ▸ hf (a+1)
  have hfj : PairFresh (B γ) (B γ') (P j ++ [.both]) 0 0 (Λ.S₀ G.1) := hPj ▸ hf (j+1)
  have hfr : PairFresh (B γ) (B γ') (P (a+1) ++ r) 0 0 (Λ.S₀ G.1) := hr ▸ hf j
  have hRead (k : ℕ) (hk : a < leftCount (P k)) :
      Λ.Bl₀ G.1 ℓ₀ ⊆ mergedTraceBlocks (B γ) (B γ') (P k) 0 0 := by
    simpa only [Nat.zero_add] using leftBlock_subset_mergedTraceBlocks (B γ) (B γ') (P k) 0 0 a hk
  have hReadA := hRead (a+1) (by rw [hLas]; omega)
  have hReadJ := hRead j (by rw [hLj]; exact haj)
  have hAp : (a-1)+1 < leftCount (P (a+1)) := by rw [hLas]; omega
  have hAp' : (a-1)+1 < rightCount (P (a+1)) := by rw [hRas]; omega
  have hAa : a < leftCount (P (a+1)) := by rw [hLas]; omega
  have hAa' : a < rightCount (P (a+1)) := by rw [hRas]; omega
  have hPrev : Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G (x,x') a =
    markedPrefixMass p q (K γ) (K γ') (P (a+1)) 0 0 (x,x')
      (fun h z => if Λ.mergedTubeMark G ℓ₀ false (P (a+1)) (a-1) (a-1) h z then 1 else 0) /
        ρ ^ sharedCount (P (a+1)) := rfl
  have hExt := Λ.firstGood_tube_mark_mass_suffix_le p q ρ κ hκ hs hsite hρ₀ γ γ' G
    (P (a+1)) r (x,x') ℓ₀ (a-1) (a-1) hAp hAp' hfr hReadA
  rw [← hr, ← hPrev] at hExt
  have hOcc (C : Finset (Vertex d)) (hC : C ∈ S) (C' : Finset (Vertex d)) (hC' : C' ∈ S) :
      markedPrefixMass p q (K γ) (K γ') (P j) 0 0 (x,x')
        (fun h z => if ¬ Λ.mergedTubeMark G ℓ₀ false (P j) (a-1) (a-1) h z ∧
          (∃ y, mergedArrivalStates? (P j) a a h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val)
          then 1 else 0) / ρ ^ sharedCount (P j) ≤ A := by
    have hcarry := Λ.firstGood_disjoint_arrival_mass_suffix_le p q ρ κ hκ hs hsite hρ₀ γ γ' G
      (P (a+1)) r (x,x') ℓ₀ (a-1) (a-1) a a hAp hAp' hAa hAa' C C' hfr hReadA
    rw [← hr] at hcarry
    refine hcarry.trans ?_
    have hbound := Λ.firstGood_shared_arrival_pair_mass_le p q ρ κ hκ hρ₀ hs hsite γ γ' z₀
      hbox hpre hcount (P a) (x,x') (by rw [hLa]; exact ha) (by rw [hRa]; exact ha)
      (by rw [hLa]; omega) (by rw [hRa]; omega) C C' (mul_nonneg hρ₀.le hA) hfa
      (by rw [hLa]; exact hasTube_target_ne hpa)
      (by rw [hRa,← hprev]; exact hasTube_target_ne hpa)
      (by simp only [hLa,hRa,← hprev]; exact hH2 C hC C' hC')
    have hcancel : ρ * A / ρ = A := by field_simp
    simp only [hLa,hRa,hcancel] at hbound
    rw [hPa]
    exact hbound
  have hAct (δ : SourceRoute D M) (i : ℕ) (hi : i < 2*M)
      (h : HasTube M (routeLab M δ.position i)) := routeSignDraw_true_of_hasTube hM δ hi h
  have hae : (a-1)+1 = a := by omega
  have hstep := Λ.firstGood_shared_predecessor_recurrence_le p q ρ κ hκ hs hsite
    hρ hρ' hM γ γ' z₀ hbox hpre hcount (P j) x x' ℓ₀ (a-1) (a-1)
    (by rw [hLj,hae]; exact haj) (by rw [hRj,hae]; exact haj)
    (by rw [hae]; exact hAct γ a (by omega) hpa)
    (by rw [hae]; exact hAct γ' a (by omega) (hprev ▸ hpa))
    hA (by rw [hLj,hRj,← hcur]) hfj hReadJ
    (by rw [hLj]; exact hj) (by rw [hRj]; exact hj)
    (by rw [hLj]; exact hasTube_target_ne hpj)
    (by rw [hRj,← hcur]; exact hasTube_target_ne hpj)
    (by rw [hLj]; exact hAct γ j (by omega) hpj)
    (by rw [hRj]; exact hAct γ' j (by omega) (hcur ▸ hpj))
    (by simp only [hLj,hRj,← hcur]; exact hrare)
    (by simp only [hLj,hRj,hArrival,hArrival']; exact hOcc)
    (by simp only [hLj]; exact hrow)
  have hstep' := hstep.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hExt (show 0 ≤ (2/3:ℝ) by norm_num)))
  simp only [hLj,hRj] at hstep'
  change markedPrefixMass p q (K γ) (K γ') (P (j+1)) 0 0 (x,x')
    (fun h z => if Λ.mergedTubeMark G ℓ false (P (j+1)) (j-1) (j-1) h z then 1 else 0) /
      ρ ^ sharedCount (P (j+1)) ≤ _
  rw [hPj]
  exact hstep'

end NearCritical.Section10.NestLayout
