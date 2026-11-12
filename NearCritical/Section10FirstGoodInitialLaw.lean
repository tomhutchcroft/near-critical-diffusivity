module

public import NearCritical.Section10FirstGoodPersistence
public import NearCritical.Section10StepBoundReduction
public import NearCritical.Section10InitialNestOverlap

/-! The actual starting row draws a uniform admissible nest and an
independent fair sign. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- At a fixed reveal the start test is certain. The normalized kernel is
uniform over the admissible initial nests and the two signs. -/
theorem firstGood_start_kernel_uniform
    (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x y : Λ.X)
    (z : Configuration d × Configuration d) :
    let ℓ := routeLab M γ.position j
    let S := Λ.fam G ℓ.site
    Λ.startCtx G ℓ →
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G j x y z =
      if y.1.val ∈ S.powersetCard Λ.k then (((S.powersetCard Λ.k).card : ℝ) * 2)⁻¹ else 0 := by
  intro ℓ S hstart
  let T := Λ.Bl₀ G.1 ℓ
  let A : Set (T → Bool) := bitSet G.2 (fun ω => Λ.succσ G ℓ x (Λ.view G.1 ℓ ω))
  let O := Λ.P.attach.filter (fun N' => N'.val.card = Λ.k ∧ N'.val ⊆ S)
  let F := fun b : T → Bool => Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  have hsep (l : RouteLabel D) : l.isStart → ¬ l.isStep ∧ ¬ l.isExit := by
    cases l <;> simp [RouteLabel.isStart, RouteLabel.isStep, RouteLabel.isExit]
  have hn := hsep ℓ hstart.1
  have hmove : ¬ Λ.moveCtx G ℓ x := fun h => hn.1 h.1
  have hexit : ¬ Λ.exitCtx G ℓ x := fun h => hn.2 h.1
  have hA : A = Set.univ := by
    ext b
    change Λ.succσ G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b)) ↔ b ∈ Set.univ
    simp [succσ,hmove,hexit]
  have hF : F = fun _ => O.product (Finset.univ : Finset Bool) := by
    funext b
    dsimp only [F]
    rw [offFirstGood, if_neg (fun h => hmove h.1), offσ,
      if_neg (fun h => hmove h.1), if_pos hstart]
    rfl
  have hOimg : O.image Subtype.val = S.powersetCard Λ.k := by
    ext N
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
      have hm := (Finset.mem_filter.mp hu).2
      exact Finset.mem_powersetCard.mpr ⟨hm.2,hm.1⟩
    · intro h
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp h
      have hP := Λ.fam_powerset_subset G hstart.2.1 (Finset.mem_powerset.mpr hsub)
      refine Finset.mem_image.mpr ⟨⟨N,hP⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hcard,hsub⟩,rfl⟩
  have hO : O.card = (S.powersetCard Λ.k).card := by
    rw [← hOimg, Finset.card_image_of_injective _ Subtype.val_injective]
  change stepKernel T A F (localSuccessProbability p q T A) y z = _
  rw [hA,hF,localSuccessProbability_univ]
  simp only [stepKernel, Set.mem_univ, true_and, Finset.mem_product, Finset.mem_univ,
    and_true, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat, one_mul, hO]
  have hmem : y.1 ∈ O ↔ y.1.val ∈ S.powersetCard Λ.k := by
    simp only [O, Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_powersetCard, and_comm]
  by_cases h : y.1 ∈ O
  · rw [if_pos h, if_pos (hmem.mp h)]
  · rw [if_neg h, if_neg (fun hn => h (hmem.mpr hn))]

/-- The initial nest marginal agrees with the uniform subset law on every
event, with no dependence on the fresh sample or incoming state. -/
theorem firstGood_initial_nest_event_weight
    (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X)
    (z : Configuration d × Configuration d) (P : Finset (Finset (Vertex d)) → Prop) [DecidablePred P] :
    let ℓ := routeLab M γ.position j
    let S := Λ.fam G ℓ.site
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    Λ.startCtx G ℓ →
    (∑ y : Λ.X, if P y.1.val then K j x y z else 0) =
      (uniformNestChoice S Λ.k).real {N | P N} := by
  intro ℓ S K hstart
  let Q := S.powersetCard Λ.k
  let O := (Finset.univ : Finset ↥Λ.P).filter fun N => N.val ∈ Q ∧ P N.val
  have hQ : (Q.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.powersetCard_nonempty.mpr hstart.2.2)
  have hsign (N : ↥Λ.P) :
      (∑ b : Bool, if P N.val then K j x (N,b) z else 0) =
        if N.val ∈ Q ∧ P N.val then (Q.card : ℝ)⁻¹ else 0 := by
    have he (b : Bool) : K j x (N,b) z =
        if N.val ∈ Q then ((Q.card : ℝ) * 2)⁻¹ else 0 :=
      Λ.firstGood_start_kernel_uniform p q ρ κ hκ hs hsiteProb γ G j x (N,b) z hstart
    by_cases hN : N.val ∈ Q <;> by_cases hP : P N.val
    · simp only [hN,hP,true_and,if_true]
      simp_rw [he, if_pos hN]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
      field_simp [hQ] <;> ring
    · simp [hP]
    · simp only [hN,hP,false_and,if_false,if_true]
      simp_rw [he, if_neg hN, Finset.sum_const_zero]
    · simp [hP]
  have hO : O.image Subtype.val = Q.filter P := by
    ext N
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr (Finset.mem_filter.mp hu).2
    · intro h
      obtain ⟨hN,hP⟩ := Finset.mem_filter.mp h
      have hsub := (Finset.mem_powersetCard.mp hN).1
      have hmem := Λ.fam_powerset_subset G hstart.2.1 (Finset.mem_powerset.mpr hsub)
      exact Finset.mem_image.mpr ⟨⟨N,hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hN,hP⟩,rfl⟩
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ N : ↥Λ.P, if N.val ∈ Q ∧ P N.val then (Q.card : ℝ)⁻¹ else 0 :=
      Finset.sum_congr rfl fun N _ => hsign N
    _ = (O.card : ℝ) / Q.card := by
      rw [← Finset.sum_filter]
      simp [O,nsmul_eq_mul,div_eq_mul_inv]
    _ = _ := by
      rw [uniformNestChoice_real_apply]
      have hc := congrArg Finset.card hO
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
      simpa only [Q, Set.mem_setOf_eq] using congrArg (fun n : ℕ => (n:ℝ) / Q.card) hc

/-- A horizontal stay has no success test and leaves the nest and
pending sign unchanged, with unit weight. -/
theorem firstGood_stay_kernel_identity (γ : SourceRoute D M) (G : Λ.Φ)
    (j : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d) :
    let ℓ := routeLab M γ.position j
    ℓ.isStep → ℓ.target = ℓ.site →
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G j x y z =
      if y = x then (1:ℝ) else 0 := by
  intro ℓ hstep hstay
  let T := Λ.Bl₀ G.1 ℓ
  let A : Set (T → Bool) := bitSet G.2 (fun ω => Λ.succσ G ℓ x (Λ.view G.1 ℓ ω))
  let F := fun b : T → Bool => Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  have hsep (l : RouteLabel D) : l.isStep → ¬ l.isStart ∧ ¬ l.isExit := by
    cases l <;> simp [RouteLabel.isStart, RouteLabel.isStep, RouteLabel.isExit]
  have hn := hsep ℓ hstep
  have hmove : ¬ Λ.moveCtx G ℓ x := fun h => h.2.1 hstay
  have hexit : ¬ Λ.exitCtx G ℓ x := fun h => hn.2 h.1
  have hA : A = Set.univ := by
    ext b
    change Λ.succσ G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b)) ↔ b ∈ Set.univ
    simp [succσ,hmove,hexit]
  have hF : F = fun _ => {x} := by
    funext b
    dsimp only [F]
    rw [offFirstGood, if_neg (fun h => hmove h.1), offσ,
      if_neg (fun h => hmove h.1), if_neg (fun h => hn.1 h.1)]
  change stepKernel T A F (localSuccessProbability p q T A) y z = _
  rw [hA,hF,localSuccessProbability_univ]
  simp [stepKernel]

/-- A stay in the history indexed by signs used on their own moves
preserves the nest and puts the inactive sign at its fixed placeholder. -/
theorem firstGood_used_stay_kernel_identity (γ : SourceRoute D M) (G : Λ.Φ)
    (active : ℕ → Bool) (j : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d)
    (hinactive : active j ≠ true) :
    let ℓ := routeLab M γ.position j
    ℓ.isStep → ℓ.target = ℓ.site →
    usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active) j x y z =
      if y.1 = x.1 ∧ y.2 = false then (1:ℝ) else 0 := by
  intro ℓ hstep hstay
  rw [Λ.firstGood_usedKernel_apply p q ρ κ hκ hs hsiteProb γ G active j x y z, if_neg hinactive]
  by_cases h : y.2 = false
  · rw [if_pos h]
    have he := Λ.firstGood_stay_kernel_identity p q ρ κ hκ hs hsiteProb γ G j
      (x.1,false) (y.1,false) z hstep hstay
    simpa [Prod.mk.injEq,h] using he
  · simp [h]

set_option maxHeartbeats 600000 in
/-- At a common root the two initial nests have the product occupation
bound, and the total weight of a root collision is at most k² / |S|. -/
theorem firstGood_common_root_collision
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (j j' : ℕ) (x x' : Λ.X)
    (z : Configuration d × Configuration d) :
    let ℓ := routeLab M γ.position j
    let S := Λ.fam G ℓ.site
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    let K' := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ' G
    let W (y : Λ.X × Λ.X) := K j x y.1 z * K' j' x' y.2 z
    routeLab M γ'.position j' = ℓ → Λ.startCtx G ℓ →
    (∀ c ∈ S, ∀ c' ∈ S, (∑ y : Λ.X × Λ.X,
      if c ∈ y.1.1.val ∧ c' ∈ y.2.1.val then W y else 0) = ((Λ.k : ℝ)/S.card)^2) ∧
    (∑ y : Λ.X × Λ.X, if (y.1.1.val ∩ y.2.1.val).Nonempty then W y else 0) ≤
      (Λ.k : ℝ)^2 / S.card := by
  intro ℓ S K K' W he hstart
  have hstart' : Λ.startCtx G (routeLab M γ'.position j') := by rw [he]; exact hstart
  have hleft (c : Finset (Vertex d)) (hc : c ∈ S) :
      (∑ y : Λ.X, if c ∈ y.1.val then K j x y z else 0) = (Λ.k : ℝ)/S.card := by
    have hp : (∑ y : Λ.X, if c ∈ y.1.val then K j x y z else 0) =
        (uniformNestChoice S Λ.k).real {N | c ∈ N} :=
      Λ.firstGood_initial_nest_event_weight p q ρ κ hκ hs hsiteProb γ G j x z (fun N => c ∈ N) hstart
    rw [hp]
    exact uniformNestChoice_mem_probability S Λ.hk hstart.2.2 hc
  have hright (c : Finset (Vertex d)) (hc : c ∈ S) :
      (∑ y : Λ.X, if c ∈ y.1.val then K' j' x' y z else 0) = (Λ.k : ℝ)/S.card := by
    have hp : (∑ y : Λ.X, if c ∈ y.1.val then K' j' x' y z else 0) =
        (uniformNestChoice (Λ.fam G (routeLab M γ'.position j').site) Λ.k).real {N | c ∈ N} :=
      Λ.firstGood_initial_nest_event_weight p q ρ κ hκ hs hsiteProb γ' G j' x' z (fun N => c ∈ N) hstart'
    rw [hp, he]
    exact uniformNestChoice_mem_probability S Λ.hk hstart.2.2 hc
  have hjoint (c : Finset (Vertex d)) (hc : c ∈ S) (c' : Finset (Vertex d)) (hc' : c' ∈ S) :
      (∑ y : Λ.X × Λ.X, if c ∈ y.1.1.val ∧ c' ∈ y.2.1.val then W y else 0) =
        ((Λ.k : ℝ)/S.card)^2 := by
    calc
      _ = (∑ y : Λ.X, if c ∈ y.1.val then K j x y z else 0) *
          (∑ y : Λ.X, if c' ∈ y.1.val then K' j' x' y z else 0) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        by_cases h : c ∈ y.1.val <;> by_cases h' : c' ∈ y'.1.val <;> simp [W,h,h']
      _ = _ := by rw [hleft c hc, hright c' hc', pow_two]
  refine ⟨hjoint,?_⟩
  have hk (y : Λ.X) : 0 ≤ K j x y z := by
    have hu : K j x y z = if y.1.val ∈ S.powersetCard Λ.k
        then (((S.powersetCard Λ.k).card : ℝ)*2)⁻¹ else 0 :=
      Λ.firstGood_start_kernel_uniform p q ρ κ hκ hs hsiteProb γ G j x y z hstart
    rw [hu]
    split_ifs <;> positivity
  have hk' (y : Λ.X) : 0 ≤ K' j' x' y z := by
    have hu : K' j' x' y z = if y.1.val ∈ (Λ.fam G (routeLab M γ'.position j').site).powersetCard Λ.k
        then ((((Λ.fam G (routeLab M γ'.position j').site).powersetCard Λ.k).card : ℝ)*2)⁻¹ else 0 :=
      Λ.firstGood_start_kernel_uniform p q ρ κ hκ hs hsiteProb γ' G j' x' y z hstart'
    rw [hu]
    split_ifs <;> positivity
  have hw (y : Λ.X × Λ.X) : 0 ≤ W y := mul_nonneg (hk y.1) (hk' y.2)
  calc
    _ ≤ ∑ y : Λ.X × Λ.X, ∑ c ∈ S, if c ∈ y.1.1.val ∧ c ∈ y.2.1.val then W y else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hW : W y = 0
      · simp [hW]
      by_cases h : (y.1.1.val ∩ y.2.1.val).Nonempty
      · obtain ⟨c,hc⟩ := h
        obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp hc
        have hvalid : y.1.1.val ∈ S.powersetCard Λ.k := by
          by_contra hn
          have hz : K j x y.1 z = 0 := by
            exact (Λ.firstGood_start_kernel_uniform p q ρ κ hκ hs hsiteProb γ G j x y.1 z hstart).trans
              (if_neg hn)
          exact hW (by simp [W,hz])
        have hcS := (Finset.mem_powersetCard.mp hvalid).1 h₁
        have hsum := Finset.single_le_sum (s := S)
          (f := fun c => if c ∈ y.1.1.val ∧ c ∈ y.2.1.val then W y else 0)
          (fun c _ => by split_ifs <;> first | exact hw y | exact le_rfl) hcS
        have hmem : (y.1.1.val ∩ y.2.1.val).Nonempty := ⟨c,hc⟩
        have hboth : c ∈ y.1.1.val ∧ c ∈ y.2.1.val := ⟨h₁,h₂⟩
        simpa only [if_pos hboth, if_pos hmem] using hsum
      · rw [if_neg h]
        exact Finset.sum_nonneg fun c _ => by split_ifs <;> first | exact hw y | exact le_rfl
    _ = ∑ c ∈ S, ((Λ.k : ℝ)/S.card)^2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c hc => hjoint c hc c hc
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      have hn : (S.card : ℝ) ≠ 0 := by
        exact_mod_cast (show S.card ≠ 0 by
          have hh : Λ.k ≤ S.card := hstart.2.2
          have hpos := Λ.hk
          omega)
      field_simp [hn] <;> ring

end NearCritical.Section10.NestLayout
