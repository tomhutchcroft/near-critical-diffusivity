module

public import NearCritical.Section10LatticeHelpers
public import NearCritical.Section10ExitProbability
public import NearCritical.Section10BoxArithmetic

/-! The step success bound, reduced to moving steps.

`NestLayout.hs_of_move`: the hypothesis `hs` of the lattice nest rule (every
step has conditional success probability at least `1/rho`) follows from

* `hmove`: the bound for MOVING steps from a `k`-nest of typical clusters
  between two cubes of the box, where success is typicality of the sprinkling
  cluster. This is exactly `prop.proba.k-nest`.
* `hexitParam`: `((1 - p)(1 - q))^m <= 1 - 1/rho` whenever
  `m >= c_b (2t)^2` (source: `(1 - p_c)^{c_b l0^2} <= eps0/4`, 5487).

Steps outside these two contexts succeed with probability one. For the exit
step the probability is computed: the exit bonds of the top patch of a typical
cluster are fresh in both layers (`exitBond_not_mem_S₀`), so the chance that
none is open is `((1 - p)(1 - q))^{|patch|}`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

lemma gluePair_layerVal_T {d : ℕ} {S T : Finset (LBond d)} (η : S → Bool)
    (z : Configuration d × Configuration d) {e : LBond d} (heT : e ∈ T) (heS : e ∉ S) :
    layerVal (gluePair η (T.restrict (layerVal z))) e = layerVal z e := by
  rw [layerVal_gluePair, dif_neg heS, dif_pos heT]
  rfl

lemma localSuccessProbability_mono {d : ℕ} (p q : unitInterval) (T : Finset (LBond d))
    {a a' : Set (T → Bool)} (h : a ⊆ a') :
    localSuccessProbability p q T a ≤ localSuccessProbability p q T a' := by
  unfold localSuccessProbability
  have hloc : ∀ s : Set (T → Bool), IsLocal T
      (fun z : Configuration d × Configuration d =>
        if T.restrict (layerVal z) ∈ s then (1:ℝ) else 0) :=
    fun s => ⟨fun b => if b ∈ s then (1:ℝ) else 0, fun _ => rfl⟩
  refine integral_mono ((hloc a).integrable p q) ((hloc a').integrable p q) (fun z => ?_)
  by_cases hz : T.restrict (layerVal z) ∈ a
  · rw [if_pos hz, if_pos (h hz)]
  · rw [if_neg hz]
    split_ifs <;> norm_num

lemma localSuccessProbability_univ {d : ℕ} (p q : unitInterval) (T : Finset (LBond d)) :
    localSuccessProbability p q T (Set.univ : Set (T → Bool)) = 1 := by
  unfold localSuccessProbability
  simp

lemma RouteLabel.not_isExit_of_isStep {D : ℕ} {ℓ : RouteLabel D} (h : ℓ.isStep) :
    ¬ ℓ.isExit := by
  cases ℓ <;> simp [RouteLabel.isStep, RouteLabel.isExit] at h ⊢

namespace NestLayout
variable {D d : ℕ} (Λ : NestLayout D d)

/-- Exit bonds of a cube of the box are not explored, in either layer. -/
lemma exitBond_not_mem_S₀ (ht : 0 < Λ.t) (F : Λ.Φ₀) {s : RSite D} (hs : s ∈ Λ.siteBox)
    {y : Vertex d} (hy : y ∈ typicalFace Λ.t (Λ.center s) (Λ.i₀, true)) (l : Bool) :
    ((l, (y, Λ.i₀)) : LBond d) ∉ Λ.S₀ F := by
  intro hmem
  unfold S₀ revealBondsOf at hmem
  obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hmem
  have hbeq : b = (y, Λ.i₀) := (Prod.mk.inj hbe).2
  rw [hbeq] at hb
  unfold clusterFamilyRevealBonds at hb
  obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨hyj, htipj, _⟩ := (mem_clusterRevealBonds _ _ _).mp hbj
  unfold typicalFace at hy
  obtain ⟨hycube, hface⟩ := Finset.mem_filter.mp hy
  have hjs : j = s := by
    by_contra hne
    exact Finset.disjoint_left.mp (Λ.hdisj hj hs hne) hyj hycube
  rw [hjs] at htipj
  have h1 := (typicalCube_int ht htipj Λ.i₀).2
  have hf : y Λ.i₀ - Λ.center s Λ.i₀ = (((Λ.t - 1) / 2 : ℕ) : ℤ) := by simpa using hface
  have htip : bondTip (y, Λ.i₀) Λ.i₀ = y Λ.i₀ + 1 := by
    unfold bondTip
    simp
  rw [htip] at h1
  linarith

theorem hs_of_move (ht : 0 < Λ.t) (M : ℕ) (p q : unitInterval) {ϱ : ℝ} (hϱ : 1 ≤ ϱ)
    (hexitParam : ∀ m : ℕ, Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ 2 ≤ (m : ℝ) →
      ((1 - (p:ℝ)) * (1 - (q:ℝ))) ^ m ≤ 1 - ϱ⁻¹)
    (hmove : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X),
      Λ.moveCtx G (routeLab M γ.position t) x → ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.moveTypical G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z)))) :
    ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))) := by
  intro γ G t x
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le one_pos hϱ
  have hinv1 : ϱ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hϱ
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = routeLab M γ.position t := ⟨_, rfl⟩
  rw [← hℓ]
  by_cases hm : Λ.moveCtx G ℓ x
  · have hnoexit : ¬ Λ.exitCtx G ℓ x := fun he => RouteLabel.not_isExit_of_isStep hm.1 he.1
    have hset : (bitSet G.2 (fun z => Λ.succσ G ℓ x (Λ.view G.1 ℓ z)) :
        Set (Λ.Bl₀ G.1 ℓ → Bool)) =
        bitSet G.2 (fun z => Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z)) := by
      ext b
      unfold bitSet succσ
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        exact h.1 hm
      · intro h
        exact ⟨fun _ => h, fun he => absurd he hnoexit⟩
    rw [hset]
    have h := hmove γ G t x (hℓ ▸ hm)
    rw [← hℓ] at h
    exact h
  · by_cases he : Λ.exitCtx G ℓ x
    · obtain ⟨hexitℓ, hlev, hsite, hcard, hsub⟩ := he
      have hne : x.1.val.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Λ.hk)
      obtain ⟨rep₀, hrep₀⟩ := hne
      have hrepfam := hsub hrep₀
      have htyp := ((mem_typicalClusterFamily _ _ _ _ _).mp hrepfam).2
      have hpatchcard := (htyp.2.2.2.2.2.1 (Λ.i₀, true) true).1
      have hexitPts : Λ.exitPts ℓ = typicalFace Λ.t (Λ.center ℓ.site) (Λ.i₀, true) := by
        unfold exitPts
        rw [if_pos ⟨hexitℓ, hlev⟩]
      have hpatchface : ∀ y ∈ Λ.exitPatch G ℓ rep₀,
          y ∈ typicalFace Λ.t (Λ.center ℓ.site) (Λ.i₀, true) := by
        intro y hy
        have h1 := typicalRegularPatch_subset_splitFace _ _ _ _ _ _ _ hy
        unfold typicalSplitFace at h1
        exact (Finset.mem_filter.mp h1).1
      obtain ⟨Y, hY⟩ : ∃ Y : Finset (Bond d),
          Y = (Λ.exitPatch G ℓ rep₀).image (fun y => ((y, Λ.i₀) : Bond d)) := ⟨_, rfl⟩
      have hYcard : Y.card = (Λ.exitPatch G ℓ rep₀).card := by
        rw [hY]
        exact Finset.card_image_of_injective _ (fun y y' h => (Prod.mk.inj h).1)
      have hYfresh : ∀ b ∈ Y, ∀ l : Bool,
          ((l, b) : LBond d) ∈ Λ.Bl₀ G.1 ℓ ∧ ((l, b) : LBond d) ∉ Λ.S₀ G.1 := by
        intro b hb l
        rw [hY] at hb
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        have hyface := hpatchface y hy
        have hnotS := Λ.exitBond_not_mem_S₀ ht G.1 hsite hyface l
        refine ⟨?_, hnotS⟩
        unfold Bl₀
        refine Finset.mem_sdiff.mpr ⟨?_, hnotS⟩
        unfold readSet
        refine Finset.mem_union_right _ ?_
        have hmem : ((y, Λ.i₀) : Bond d) ∈ (Λ.exitPts ℓ).image (fun y => ((y, Λ.i₀) : Bond d)) := by
          rw [hexitPts]
          exact Finset.mem_image_of_mem _ hyface
        unfold bothLayers
        cases l
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmem)
      -- the smaller success set: some exit bond of the patch is open
      have hsubset : (bitSet G.2 (fun z => ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true) :
          Set (Λ.Bl₀ G.1 ℓ → Bool)) ⊆
          bitSet G.2 (fun z => Λ.succσ G ℓ x (Λ.view G.1 ℓ z)) := by
        intro b hb
        obtain ⟨bd, hbd, hopen⟩ := hb
        rw [hY] at hbd
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbd
        refine ⟨fun hmc => absurd hmc hm, fun _ => ⟨rep₀, hrep₀, y, hy, ?_⟩⟩
        unfold view
        refine Finset.mem_filter.mpr ⟨?_, hopen⟩
        rw [hexitPts]
        exact hpatchface y hy
      have hprob : localSuccessProbability p q (Λ.Bl₀ G.1 ℓ)
          (bitSet G.2 (fun z => ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true)) =
          1 - ((1 - (p:ℝ)) * (1 - (q:ℝ))) ^ Y.card := by
        rw [← exists_open_integral p q Y]
        unfold localSuccessProbability
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        have hiff : ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z) ∈
            (bitSet G.2 (fun z => ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true) :
              Set (Λ.Bl₀ G.1 ℓ → Bool))) ↔
            ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true := by
          have hval : ∀ b ∈ Y, sprinkleOrConfiguration
              (gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))).1
              (gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))).2 b =
              sprinkleOrConfiguration z.1 z.2 b := by
            intro b hb
            have h1 := gluePair_layerVal_T G.2 z (hYfresh b hb false).1 (hYfresh b hb false).2
            have h2 := gluePair_layerVal_T G.2 z (hYfresh b hb true).1 (hYfresh b hb true).2
            unfold sprinkleOrConfiguration
            have h1' : (gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))).1 b = z.1 b := h1
            have h2' : (gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))).2 b = z.2 b := h2
            rw [h1', h2']
          constructor
          · rintro ⟨b, hb, hopen⟩
            exact ⟨b, hb, (hval b hb) ▸ hopen⟩
          · rintro ⟨b, hb, hopen⟩
            exact ⟨b, hb, (hval b hb).symm ▸ hopen⟩
        beta_reduce
        by_cases hz : ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true
        · rw [if_pos (hiff.mpr hz), if_pos hz]
        · rw [if_neg (fun h => hz (hiff.mp h)), if_neg hz]
      have hparam := hexitParam Y.card (by rw [hYcard]; exact hpatchcard)
      calc ϱ⁻¹ ≤ 1 - ((1 - (p:ℝ)) * (1 - (q:ℝ))) ^ Y.card := by linarith
        _ = _ := hprob.symm
        _ ≤ _ := localSuccessProbability_mono p q _ hsubset
    · have hset : (bitSet G.2 (fun z => Λ.succσ G ℓ x (Λ.view G.1 ℓ z)) :
          Set (Λ.Bl₀ G.1 ℓ → Bool)) = Set.univ := by
        ext b
        unfold bitSet succσ
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact ⟨fun h => absurd h hm, fun h => absurd h he⟩
      rw [hset, localSuccessProbability_univ]
      exact hinv1

end NestLayout
end NearCritical.Section10
