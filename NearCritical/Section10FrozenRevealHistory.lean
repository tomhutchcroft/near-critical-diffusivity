module

public import NearCritical.Section10FirstGoodPairUsedHistory
public import NearCritical.Section10FirstGoodPersistence
public import NearCritical.Section10MergedTraceLocal

/-! A fresh history can be tested on a sample realizing the fixed
reveal, without changing any of the history's fresh bits. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- Gluing a fresh block to a realized reveal retains the reveal atom and
agrees with the fresh sample on the block. -/
theorem refineReveal_glue_fresh {d : ℕ} {Φ : Type*}
    (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (z₀ z : Configuration d × Configuration d) (T : Finset (LBond d)) :
    let G := refineReveal ρ S z₀
    let w := gluePair G.2 (T.restrict (layerVal z))
    Disjoint (S G.1) T →
    refineReveal ρ S w = G ∧ ∀ e ∈ T, layerVal w e = layerVal z e := by
  intro G w hd
  have hreveal : (S G.1).restrict (layerVal w) = (S G.1).restrict (layerVal z₀) := by
    funext e
    change layerVal w e.val = layerVal z₀ e.val
    dsimp only [w]
    rw [layerVal_gluePair, dif_pos e.property]
    rfl
  obtain ⟨f,hf⟩ := refineReveal_atom_isLocal ρ S hρ G
  have hatom : (if refineReveal ρ S w = G then (1:ℝ) else 0) =
      (if refineReveal ρ S z₀ = G then (1:ℝ) else 0) :=
    (hf w).trans ((congrArg f hreveal).trans (hf z₀).symm)
  refine ⟨?_, ?_⟩
  · by_contra h
    have hz₀ : refineReveal ρ S z₀ = G := rfl
    rw [if_neg h, if_pos hz₀] at hatom
    exact zero_ne_one hatom
  · intro e he
    have hs : e ∉ S G.1 := fun hs => Finset.disjoint_left.mp hd hs he
    dsimp only [w]
    rw [layerVal_gluePair, dif_neg hs, dif_pos he]
    rfl

/-- A positive joint history preserves the two validity invariants at
their own clocks. A solo row leaves the other route's state in place. -/
theorem mergedTraceLast_valid_of_pos {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ) (z : Ω)
    (hK : ∀ t x y w, 0 ≤ k t x y w) (hK' : ∀ t x y w, 0 ≤ k' t x y w)
    (A : ℕ → X → Prop) (B : ℕ → Y → Prop)
    (hA : ∀ t x y, A t x → 0 < k t x y z → A (t+1) y)
    (hB : ∀ t x y, B t x → 0 < k' t x y z → B (t+1) y)
    (s : List PairMove) (t t' : ℕ) (x : X × Y) (h : NestTrace (X × Y) s.length)
    (hx : A t x.1) (hx' : B t' x.2) (hw : 0 < mergedTraceMass k k' z s t t' x h) :
    A (t + leftCount s) (mergedTraceLast s x h).1 ∧
      B (t' + rightCount s) (mergedTraceLast s x h).2 := by
  induction s generalizing t t' x with
  | nil => simpa only [leftCount, rightCount, Nat.add_zero, mergedTraceLast] using And.intro hx hx'
  | cons m s ih =>
    change 0 < pairMoveKernel k k' m t t' x h.1 z *
      mergedTraceMass k k' z s (m.nextLeft t) (m.nextRight t') h.1 h.2 at hw
    have hrest : 0 ≤ mergedTraceMass k k' z s (m.nextLeft t) (m.nextRight t') h.1 h.2 :=
      mergedTraceMass_nonneg k k' hK hK'
        z s (m.nextLeft t) (m.nextRight t') h.1 h.2
    have hrow := pos_of_mul_pos_left hw hrest
    have hnext : A (m.nextLeft t) h.1.1 ∧ B (m.nextRight t') h.1.2 := by
      cases m
      · change 0 < (if h.1.2 = x.2 then k t x.1 h.1.1 z else 0) at hrow
        split_ifs at hrow with he
        · exact ⟨hA t x.1 h.1.1 hx hrow, he.symm ▸ hx'⟩
        · exact (lt_irrefl _ hrow).elim
      · change 0 < (if h.1.1 = x.1 then k' t' x.2 h.1.2 z else 0) at hrow
        split_ifs at hrow with he
        · exact ⟨he.symm ▸ hx, hB t' x.2 h.1.2 hx' hrow⟩
        · exact (lt_irrefl _ hrow).elim
      · change 0 < k t x.1 h.1.1 z * k' t' x.2 h.1.2 z at hrow
        exact ⟨hA t x.1 h.1.1 hx (pos_of_mul_pos_left hrow (hK' _ _ _ _)),
          hB t' x.2 h.1.2 hx' (pos_of_mul_pos_right hrow (hK _ _ _ _))⟩
    have hs := ih (m.nextLeft t) (m.nextRight t') h.1 h.2 hnext.1 hnext.2
      (pos_of_mul_pos_right hw hrow.le)
    cases m <;> simpa only [PairMove.nextLeft, PairMove.nextRight, leftCount, rightCount,
      mergedTraceLast, Nat.add_assoc, Nat.add_comm 1] using hs

namespace NestLayout

/-- Apply the gluing identity to the actual critical exploration reveal. -/
theorem firstGood_glue_fresh_reveal {D d : ℕ} (Λ : NestLayout D d)
    (z₀ z : Configuration d × Configuration d) (T : Finset (LBond d)) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let w := gluePair G.2 (T.restrict (layerVal z))
    Disjoint (Λ.S₀ G.1) T →
    refineReveal Λ.ρ₀ Λ.S₀ w = G ∧ ∀ e ∈ T, layerVal w e = layerVal z e :=
  refineReveal_glue_fresh Λ.ρ₀ Λ.S₀
    (criticalReveal_atom_isLocal Λ.siteBox Λ.Q Λ.Hh Λ.hdisj (fun j _ => Λ.hH j)) z₀ z T

/-- At a fixed realized reveal, positive fresh histories end in admissible
nests, even when the sample on which their kernel weights are evaluated
has a different reveal. -/
theorem firstGood_frozen_prefix_valid {D d M : ℕ} (Λ : NestLayout D d)
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
    let Valid (δ : SourceRoute D M) j (u : Λ.X) := 0 < j → j < 2*M →
      u.1.val.card = Λ.k ∧ u.1.val ⊆ Λ.fam G (routeLab M δ.position j).site
    Disjoint (Λ.S₀ G.1) (mergedTraceBlocks (B γ) (B γ') s 0 0) →
    0 < mergedTraceMass (K γ) (K γ') z s 0 0 x h →
    Valid γ (leftCount s) (mergedTraceLast s x h).1 ∧
      Valid γ' (rightCount s) (mergedTraceLast s x h).2 := by
  intro G B K Valid hd hw
  let T := mergedTraceBlocks (B γ) (B γ') s 0 0
  let w := gluePair G.2 (T.restrict (layerVal z))
  obtain ⟨hG,hwz⟩ := Λ.firstGood_glue_fresh_reveal z₀ z T hd
  have hLocal (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (K δ j u v) :=
    stepKernel_isLocal _ _ _ _ v
  have hK₀ (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) (v₀ : Configuration d × Configuration d) :
      0 ≤ K δ j u v v₀ :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G j u)) v v₀
  obtain ⟨f,hf⟩ := mergedTraceMass_isLocal (B γ) (B γ') (K γ) (K γ')
    (hLocal γ) (hLocal γ') s 0 0 x h
  have he : T.restrict (layerVal w) = T.restrict (layerVal z) := funext fun e => hwz e.val e.property
  have hm : mergedTraceMass (K γ) (K γ') w s 0 0 x h =
      mergedTraceMass (K γ) (K γ') z s 0 0 x h :=
    (hf w).trans ((congrArg f he).trans (hf z).symm)
  have hp : 0 < mergedTraceMass (K γ) (K γ') w s 0 0 x h := by
    rw [hm]
    exact hw
  have hnext (δ : SourceRoute D M) (hδ : δ ∈ ({γ,γ'} : Finset (SourceRoute D M)))
      (j : ℕ) (u v : Λ.X) (hu : Valid δ j u) (hp₀ : 0 < K δ j u v w) :
      Valid δ (j+1) v := by
    intro _ hj
    have hprew (i : ℕ) (hi : i < 2*M) :
        IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) w.1 := by
      apply (Λ.goodCube_iff w (hbox δ hδ i hi)).mp
      rw [hG]
      exact (Λ.goodCube_iff z₀ (hbox δ hδ i hi)).mpr (hpre δ hδ i hi)
    have h := Λ.firstGood_route_next_valid δ w p q ρ κ hκ hs hsite
      (hbox δ hδ) hprew hcount j hj u v
    have hinput (hj₀ : 1 ≤ j) : u.1.val.card = Λ.k ∧
        u.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ w) (routeLab M δ.position j).site := by
      rw [hG]
      exact hu (by omega) (by omega)
    have hpos : 0 < (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
        δ (refineReveal Λ.ρ₀ Λ.S₀ w) j u v w := by
      rw [hG]
      exact hp₀
    have hv := h hinput hpos
    rw [hG] at hv
    exact hv
  simpa only [Nat.zero_add] using
    mergedTraceLast_valid_of_pos (K γ) (K γ') w (hK₀ γ) (hK₀ γ')
      (Valid γ) (Valid γ') (hnext γ (by simp)) (hnext γ' (by simp)) s 0 0 x h
      (fun h₀ _ => (Nat.lt_irrefl _ h₀).elim) (fun h₀ _ => (Nat.lt_irrefl _ h₀).elim) hp

/-- Moving the sign draw to the row that uses it preserves every marked
sum at a frozen reveal, on any sample of its fresh blocks. -/
theorem firstGood_frozen_merged_marked_sum_fixedStart
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
    (F : NestTrace Λ.X (leftCount s) → NestTrace Λ.X (rightCount s) → ℝ) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let L (δ : SourceRoute D M) := usedMaskedKernel (routeSignDraw δ)
      (Λ.firstGoodMaskBase p q ρ κ hκ hs hsite δ G (routeSignDraw δ))
    let U (δ : SourceRoute D M) n a (h : NestTrace Λ.X n) :=
      eraseInitialUsedSign n (usedMaskedTrace (routeSignDraw δ) n 0 a h)
    Disjoint (Λ.S₀ G.1) (mergedTraceBlocks (B γ) (B γ') s 0 0) →
    (∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F (U γ (leftCount s) x.2 (mergedRouteTraces s h).1)
        (U γ' (rightCount s) x'.2 (mergedRouteTraces s h).2) *
        mergedTraceMass (K γ) (K γ') z s 0 0 (x,x') h) =
    ∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F (eraseInitialUsedSign (leftCount s) (mergedRouteTraces s h).1)
        (eraseInitialUsedSign (rightCount s) (mergedRouteTraces s h).2) *
        mergedTraceMass (L γ) (L γ') z s 0 0 ((x.1,b),(x'.1,b')) h := by
  intro G B K L U hd
  let T := mergedTraceBlocks (B γ) (B γ') s 0 0
  let w := gluePair G.2 (T.restrict (layerVal z))
  obtain ⟨hG,hwz⟩ := Λ.firstGood_glue_fresh_reveal z₀ z T hd
  have hprew (δ : SourceRoute D M) (hδ : δ ∈ ({γ,γ'} : Finset (SourceRoute D M)))
      (i : ℕ) (hi : i < 2*M) :
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) w.1 := by
    apply (Λ.goodCube_iff w (hbox δ hδ i hi)).mp
    rw [hG]
    exact (Λ.goodCube_iff z₀ (hbox δ hδ i hi)).mpr (hpre δ hδ i hi)
  have he : T.restrict (layerVal w) = T.restrict (layerVal z) := funext fun e => hwz e.val e.property
  have hKloc (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (K δ j u v) :=
    stepKernel_isLocal _ _ _ _ v
  have hLloc (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (L δ j u v) :=
    Λ.firstGood_usedKernel_isLocal p q ρ κ hκ hs hsite δ G (routeSignDraw δ) j u v
  have hsame
      (J : SourceRoute D M → ℕ → Λ.X → Λ.X → Configuration d × Configuration d → ℝ)
      (hJ : ∀ δ j u v, IsLocal (B δ j) (J δ j u v))
      (u : Λ.X × Λ.X) (h : NestTrace (Λ.X × Λ.X) s.length) :
      mergedTraceMass (J γ) (J γ') w s 0 0 u h = mergedTraceMass (J γ) (J γ') z s 0 0 u h := by
    obtain ⟨f,hf⟩ := mergedTraceMass_isLocal (B γ) (B γ') (J γ) (J γ')
      (hJ γ) (hJ γ') s 0 0 u h
    exact (hf w).trans ((congrArg f he).trans (hf z).symm)
  have hmark := Λ.firstGood_merged_marked_sum_fixedStart p q ρ κ hκ hs hsite
    γ γ' w hM hbox hprew hcount s x x' b b' F
  dsimp only at hmark
  rw [hG] at hmark
  change (∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F (U γ (leftCount s) x.2 (mergedRouteTraces s h).1)
        (U γ' (rightCount s) x'.2 (mergedRouteTraces s h).2) *
        mergedTraceMass (K γ) (K γ') w s 0 0 (x,x') h) =
    ∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F (eraseInitialUsedSign (leftCount s) (mergedRouteTraces s h).1)
        (eraseInitialUsedSign (rightCount s) (mergedRouteTraces s h).2) *
        mergedTraceMass (L γ) (L γ') w s 0 0 ((x.1,b),(x'.1,b')) h at hmark
  simpa only [hsame K hKloc, hsame L hLloc] using hmark

end NestLayout
end NearCritical.Section10
