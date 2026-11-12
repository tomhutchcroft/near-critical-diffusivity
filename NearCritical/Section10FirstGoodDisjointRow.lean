module

public import NearCritical.Section10FirstGoodOccupationRow
public import NearCritical.Section10FirstGoodPhaseRow
public import NearCritical.Section10DisjointOffspringTranslation
public import NearCritical.Section10DisjointNestOccupation

/-! Joint occupation of two prescribed children on a shared fresh tube,
restricted to the event that the two whole-nest bridges are disjoint. -/

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

/-- The product of the normalized outgoing masses on the disjoint-bridge
event satisfies the H2 bound after summing over potential representatives. -/
theorem firstGood_disjoint_child_pair_row_le (hρ : 0 < ρ)
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (j j' : ℕ) (x x' : Λ.X)
    (c c' : Finset (Vertex d)) {a : ℝ} :
    let ℓ := routeLab M γ.position j
    let μ := (percolation d p).prod (percolation d q)
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
    let U (δ : SourceRoute D M) (i : ℕ) (v : Λ.X) (b : Finset (Vertex d)) z :=
      ∑ y : Λ.X, if b ∈ y.1.val then R.kernel δ G i v y z else 0
    routeLab M γ'.position j' = ℓ →
    Disjoint (Λ.readSet G.1 ℓ) (Λ.S₀ G.1) →
    Λ.moveCtx G ℓ x → Λ.moveCtx G ℓ x' →
    Λ.Mid ℓ ⊆ Λ.L ℓ →
    Disjoint (Λ.Mid ℓ : Set (Vertex d)) (Λ.Q ℓ.site : Set (Vertex d)) →
    (∀ A ∈ x.1.val, ∀ A' ∈ x'.1.val,
      μ.real (disjointOffspringEvent (orientedLatticePairs (Λ.Mid ℓ)) (Λ.L ℓ) (Λ.R ℓ)
        (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
        (Λ.src G ℓ x.2 A) (Λ.src G ℓ x'.2 A') (Λ.tgt G ℓ c) (Λ.tgt G ℓ c')
        (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))) ≤ a) →
    (∫ z, if Λ.firstGoodSharedTubeMark G ℓ x.1.val x'.1.val x.2 x'.2 z
      then 0 else U γ j x c z * U γ' j' x' c' z ∂μ) ≤
      ρ^2 * ((x.1.val.card : ℝ) * (x'.1.val.card : ℝ) * a) := by
  intro ℓ μ R U hℓ hfresh hx hx' hML hMQ hrare
  let V := stepView (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ)
    (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
  let B (v : Λ.X) (z : Configuration d × Configuration d) :=
    section9SprinklingCluster z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs (Λ.Mid ℓ))
      (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
      (sprinklingTargetBoundary v.1.val (Λ.src G ℓ v.2))
      (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))
  let HasChild (z : Configuration d × Configuration d) (v : Λ.X) (b : Finset (Vertex d)) :=
    ∃ N ∈ svNext (V z) v.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ v.2) (Λ.tgt G ℓ) Λ.k Λ.P, b ∈ N.val
  let E := {z | HasChild z x c ∧ HasChild z x' c' ∧ Disjoint (B x z) (B x' z)}
  have hB (v : Λ.X) (z : Configuration d × Configuration d) :
      B v z = Λ.firstGoodNestBridge G ℓ v.1.val v.2 z :=
    middle_sprinklingCluster_or_eq z.1 z.2 _ _ _ _ _ _ _ _ _ hML hMQ
  have hloc : ReadsOnly
      (stepReadSet (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ)
        (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target))
      (fun z => z ∈ E) := by
    intro z z' hz
    have hv : V z = V z' := stepView_readsOnly _ _ _ _ _ _ _ z z' hz
    have hb (v : Λ.X) : B v z = B v z' := by
      rw [hB, hB]
      exact rawBridge_readsOnly _ _ _ _ _ _ _ _ _ z z' hz
    change (HasChild z x c ∧ HasChild z x' c' ∧ Disjoint (B x z) (B x' z)) =
      (HasChild z' x c ∧ HasChild z' x' c' ∧ Disjoint (B x z') (B x' z'))
    simp only [HasChild, hv, hb]
  have hE : MeasurableSet E := hloc.measurableSet
  have hprob : μ.real E ≤ (x.1.val.card : ℝ) * (x'.1.val.card : ℝ) * a :=
    svNext_disjoint_pair_occupation_le μ (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ)
      (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target) hML hMQ
      x.1.val x'.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2) (Λ.src G ℓ x'.2)
      (Λ.tgt G ℓ) Λ.k Λ.P c c' hrare
  have hrows (δ : SourceRoute D M) (i : ℕ) (v : Λ.X) (z : Configuration d × Configuration d) :
      (∀ y, 0 ≤ R.kernel δ G i v y z) ∧ (∑ y, R.kernel δ G i v y z) ≤ ρ := by
    let T := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let S : Set (T → Bool) := R.a δ G i v
    let O : (T → Bool) → Finset Λ.X := R.o δ G i v
    let s := localSuccessProbability p q T S
    have hs' : ρ⁻¹ ≤ s := hs δ G i v
    have hs₀ : 0 < s := (inv_pos.mpr hρ).trans_le hs'
    refine ⟨fun y => stepKernel_nonneg T S O hs₀.le y z, ?_⟩
    change (∑ y : Λ.X, stepKernel T S O s y z) ≤ ρ
    rw [stepKernel_sum T S O (R.ho δ G i v)]
    split_ifs
    · simpa only [one_mul] using (inv_le_comm₀ hs₀ hρ).mpr hs'
    · simpa only [zero_mul] using hρ.le
  have hU (δ : SourceRoute D M) (i : ℕ) (v : Λ.X) (b : Finset (Vertex d))
      (z : Configuration d × Configuration d) : 0 ≤ U δ i v b z ∧ U δ i v b z ≤ ρ := by
    obtain ⟨hn, hc⟩ := hrows δ i v z
    refine ⟨Finset.sum_nonneg (fun y _ => ?_), (Finset.sum_le_sum fun y _ => ?_).trans hc⟩
    · split_ifs <;> first | exact hn y | exact le_rfl
    · split_ifs <;> first | exact le_rfl | exact hn y
  have hchild (δ : SourceRoute D M) (i : ℕ) (v : Λ.X) (b : Finset (Vertex d))
      (z : Configuration d × Configuration d)
      (heq : routeLab M δ.position i = ℓ) (hm : Λ.moveCtx G ℓ v)
      (hpos : 0 < U δ i v b z) : HasChild z v b := by
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    by_cases hyb : b ∈ y.1.val
    · have hky := lt_of_le_of_ne ((hrows δ i v z).1 y) (by
        simpa only [if_pos hyb] using Ne.symm hy)
      have hh := Λ.firstGood_positive_svNext_of_fresh p q ρ κ hκ hs hsiteProb δ G i v y z
      dsimp only at hh
      rw [heq] at hh
      exact ⟨y.1, hh hfresh hm hky, hyb⟩
    · simp [hyb] at hy
  calc
    _ ≤ ∫ z, E.indicator (fun _ => ρ^2) z ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
        ((integrable_const _).indicator hE) (Filter.Eventually.of_forall ?_)
      · intro z
        dsimp only
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hU γ j x c z).1 (hU γ' j' x' c' z).1
      · intro z
        dsimp only
        by_cases hz : z ∈ E
        · rw [Set.indicator_of_mem hz]
          split_ifs
          · exact sq_nonneg ρ
          · rw [pow_two]
            exact mul_le_mul (hU γ j x c z).2 (hU γ' j' x' c' z).2 (hU γ' j' x' c' z).1 hρ.le
        · rw [Set.indicator_of_notMem hz]
          split_ifs with hm
          · exact le_rfl
          · by_contra! hp
            have hu := pos_of_mul_pos_left hp (hU γ' j' x' c' z).1
            have hu' := pos_of_mul_pos_right hp (hU γ j x c z).1
            have hdis : Disjoint (B x z) (B x' z) := by
              rw [hB, hB]
              exact Finset.disjoint_left.mpr (fun v hv hv' => hm
                ((Λ.firstGoodSharedTubeMark_iff_raw_of_fresh G ℓ hfresh _ _ _ _ z).2
                  ⟨v, Finset.mem_inter.mpr ⟨hv,hv'⟩⟩))
            exact hz ⟨hchild γ j x c z rfl hx hu, hchild γ' j' x' c' z hℓ hx' hu', hdis⟩
    _ = μ.real E * ρ^2 := by rw [integral_indicator_const _ hE, smul_eq_mul]
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hprob (sq_nonneg ρ)

end NearCritical.Section10.NestLayout

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

/-- H2 for the actual normalized first-good rule. The estimate holds for
every prescribed pair of children and both incoming pending signs. -/
theorem actualLayout_firstGood_disjoint_child_pair_row {D : ℕ}
    [LinearOrder (Finset (Vertex (D+1)))]
    (hd : 2 ≤ D+1) (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D+1) : ℝ)) (hp1 : (criticalPoint (D+1) : ℝ) < 1)
    (typ : TypicalParameters) (hb : 0 ≤ typ.boundaryUpper) :
    ∃ C : ℝ, ∀ (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      let p := criticalPoint (D+1)
      ∀ (q : unitInterval), (q:ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
      ∀ (ρ κ : ℝ) (hκ : 0 < κ), 0 < ρ →
      ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
        localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
          (bitSet G.2 (fun w => Λ.succσ G (routeLab M γ.position j) x
            (Λ.view G.1 (routeLab M γ.position j) w))))
        (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
        (G : Λ.Φ) (γ γ' : SourceRoute D M) (j j' : ℕ) (x x' : Λ.X)
        (c c' : Finset (Vertex (D+1))),
      let ℓ := routeLab M γ.position j
      let μ := (percolation (D+1) p).prod (percolation (D+1) q)
      let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
      let U (δ : SourceRoute D M) (i : ℕ) (v : Λ.X) (b : Finset (Vertex (D+1))) z :=
        ∑ y : Λ.X, if b ∈ y.1.val then R.kernel δ G i v y z else 0
      routeLab M γ'.position j' = ℓ → Λ.moveCtx G ℓ x → Λ.moveCtx G ℓ x' →
      c ∈ Λ.fam G ℓ.target → c' ∈ Λ.fam G ℓ.target →
      (∫ z, if Λ.firstGoodSharedTubeMark G ℓ x.1.val x'.1.val x.2 x'.2 z
        then 0 else U γ j x c z * U γ' j' x' c' z ∂μ) ≤
        ρ^2 * ((k:ℝ)^2 * (C * (t:ℝ)^(12-2*((D+1:ℕ):ℝ)))) := by
  obtain ⟨C,hC⟩ := actualLayout_disjoint_offspring_probability hd asymp q₀ hp0 hp1 typ hb
  refine ⟨C,?_⟩
  intro t ht k hk MOff Mcoal Kdiam M Λ p q hq ρ κ hκ hρ hs hsiteProb G γ γ' j j' x x' c c'
    ℓ μ R U hℓ hx hx' hc hc'
  have hctx := hx
  obtain ⟨hstep,hmove,hsite,htgt,hcard,hnest,_,_,z,hz⟩ := hx
  have hnest' := hx'.2.2.2.2.2.1
  have hcard' := hx'.2.2.2.2.1
  have hTube : HasTube M ℓ := routeLab_hasTube γ.1.1 γ.2 hstep hmove
  have hnoexit : ¬ ℓ.isExit := by
    have he (l : RouteLabel D) : l.isStep → ¬ l.isExit := by
      cases l <;> simp [RouteLabel.isStep, RouteLabel.isExit]
    exact he ℓ hstep
  have hM := actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hTube
  have hL := actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hTube
  have hQ := actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ
  have hML : Λ.Mid ℓ ⊆ Λ.L ℓ := by
    rw [hM,hL]
    apply translateSites_mono
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have hMQ : Disjoint (Λ.Mid ℓ) (Λ.Q ℓ.site) := by
    rw [hM,hQ]
    exact (Finset.disjoint_image (add_right_injective _)).mpr
      (section9FiniteMiddle_disjoint_first _ (by omega))
  have hMQ' : Disjoint (Λ.Mid ℓ : Set (Vertex (D+1))) (Λ.Q ℓ.site : Set (Vertex (D+1))) :=
    Finset.disjoint_coe.mpr hMQ
  subst G
  have hh := Λ.firstGood_disjoint_child_pair_row_le p q ρ κ hκ hs hsiteProb hρ
    γ γ' (refineReveal Λ.ρ₀ Λ.S₀ z) j j' x x' c c' hℓ
    (actualLayout_readSet_disjoint D typ t ht k hk MOff Mcoal Kdiam M (Λ.ρ₀ z) ℓ hnoexit)
    hctx hx' hML hMQ' (fun A hA A' hA' => hC t ht k hk MOff Mcoal Kdiam M z ℓ hTube
      hsite htgt q hq A A' c c' x.2 x'.2 (hnest hA) (hnest' hA') hc hc')
  change x.1.val.card = k at hcard
  change x'.1.val.card = k at hcard'
  simpa only [hcard,hcard',pow_two] using hh

end NearCritical.Section10
