module

public import NearCritical.Section10StepHypotheses
public import NearCritical.Section10Section9Regularity

/-! Data of a step of the actual layout as translates of the Section 9 origin
sets, and the pulled-back face-core conditions.

With `a = siteCenter t l.site`, `i = dirOf l`, `n = t`, for a label with a tube:

* `actual_Mid_eq`, `actual_L_eq`, `actual_R_eq`, `actual_Qsite_eq`,
  `actual_Qtarget_eq`: middle region, tubes and the two cubes are the
  translates by `a` of the Section 9 sets;
* `NestLayout.heartUnion_revealConfig`: for a realised reveal, the cluster union
  computed from the reveal configuration is the revealed set of the cube;
* `actual_src_pullback_core`, `actual_tgt_pullback_core`: pulled back by `-a`,
  source patches lie in the positive face core and target patches in the
  negative face core.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

section realised
variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.heartUnion_revealConfig (z : Configuration d × Configuration d)
    {s : RSite D} (hs : s ∈ Λ.siteBox) :
    heartClusterUnion (Λ.revealConfig (refineReveal Λ.ρ₀ Λ.S₀ z)) (Λ.Q s) (Λ.Hh s) =
      Λ.Fat (Λ.ρ₀ z) s := by
  rw [Λ.Fat_realised z hs]
  exact heartClusterUnion_eq_of_reveal_agree (Λ.Q s) (Λ.Hh s) _ (Λ.hH s) rfl
    (fun e he => (Λ.revealConfig_eq z e (Λ.mem_S₀ z hs he)).symm)

end realised

section actual
variable {D : ℕ} (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
  (MOff Mcoal Kdiam M : ℕ)

lemma actual_Mid_eq {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) :
    (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Mid ℓ =
      translateSites (siteCenter t ℓ.site) (section9FiniteMiddle (dirOf ℓ) t) := by
  show MidOf t M ℓ = _
  unfold MidOf
  rw [if_pos hℓ]
  rfl

lemma actual_L_eq {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) :
    (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).L ℓ =
      translateSites (siteCenter t ℓ.site)
        (section9FiniteTube (dirOf ℓ) t (-(5 : ℝ)/8) (3/8)) := by
  show LOf t M ℓ = _
  unfold LOf
  rw [if_pos hℓ]
  rfl

lemma actual_R_eq {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) :
    (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).R ℓ =
      translateSites (siteCenter t ℓ.site)
        (section9FiniteTube (dirOf ℓ) t (-(3 : ℝ)/8) (5/8)) := by
  show ROf t M ℓ = _
  unfold ROf
  rw [if_pos hℓ]
  rfl

lemma actual_Qsite_eq (ℓ : RouteLabel D) :
    (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Q ℓ.site =
      translateSites (siteCenter t ℓ.site) (section9FiniteEndCube (dirOf ℓ) t 0) := by
  show typicalCube t (siteCenter t ℓ.site) = _
  have h := typicalCube_translate t (siteCenter t ℓ.site) (0 : Vertex (D + 1))
  rw [add_zero] at h
  rw [h, typicalCube_zero_eq_endCube (by omega) (dirOf ℓ)]

lemma farCenter_eq_add {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    farCenter t c i = c + farCenter t (0 : Vertex d) i := by
  unfold farCenter
  rw [zero_add]

lemma actual_Qtarget_eq {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) :
    (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Q ℓ.target =
      translateSites (siteCenter t ℓ.site)
        (section9FiniteEndCube (dirOf ℓ) t (2 * (t : ℝ))) := by
  show typicalCube t (siteCenter t ℓ.target) = _
  rw [siteCenter_target t hℓ, farCenter_eq_add, typicalCube_translate,
    typicalCube_far_eq_endCube (by omega) (dirOf ℓ)]

lemma mem_translateSites_neg {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) {x : Vertex d}
    (hx : x ∈ translateSites (-a) (translateSites a U)) : x ∈ U := by
  obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff (-a) _ x).mp hx
  obtain ⟨w, hw, rfl⟩ := (mem_translateSites_iff a U y).mp hy
  rw [neg_add_cancel_left]
  exact hw

lemma translateSites_mono {d : ℕ} (a : Vertex d) {U V : Finset (Vertex d)} (h : U ⊆ V) :
    translateSites a U ⊆ translateSites a V :=
  Finset.image_subset_image h

theorem actual_src_pullback_core (G : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Φ)
    (ℓ : RouteLabel D) (pl : Bool) (nest : Finset (Finset (Vertex (D + 1)))) :
    ∀ x ∈ translateSites (-(siteCenter t ℓ.site))
        (sprinklingTargetBoundary nest
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).src G ℓ pl)),
      x ∈ section8ExtensionPositiveFaceCore (dirOf ℓ) t := by
  intro x hx
  have hsub : sprinklingTargetBoundary nest
      ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).src G ℓ pl) ⊆
      translateSites (siteCenter t ℓ.site)
        (typicalSplitFace t (0 : Vertex (D + 1)) (dirOf ℓ, true) pl) := by
    unfold sprinklingTargetBoundary
    refine Finset.biUnion_subset.mpr (fun C _ y hy => ?_)
    have h1 : y ∈ typicalSplitFace t (siteCenter t ℓ.site) (dirOf ℓ, true) pl :=
      (Finset.mem_inter.mp (Finset.mem_filter.mp hy).1).2
    have h2 := typicalSplitFace_translate t (siteCenter t ℓ.site) (0 : Vertex (D + 1))
      (dirOf ℓ, true) pl
    rw [add_zero] at h2
    rw [← h2]
    exact h1
  exact splitFace_subset_positiveFaceCore (by omega) (dirOf ℓ) pl
    (mem_translateSites_neg _ _ (translateSites_mono _ hsub hx))

theorem actual_tgt_pullback_core (G : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Φ)
    {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) (C : Finset (Vertex (D + 1))) :
    ∀ y ∈ translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).tgt G ℓ C),
      y ∈ section8ExtensionNegativeFaceCore (dirOf ℓ) t := by
  intro y hy
  have hsplit : ∀ pl : Bool, typicalSplitFace t (siteCenter t ℓ.target) (dirOf ℓ, false) pl =
      translateSites (siteCenter t ℓ.site)
        (typicalSplitFace t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) (dirOf ℓ, false) pl) := by
    intro pl
    rw [siteCenter_target t hℓ, farCenter_eq_add, typicalSplitFace_translate]
  have hmem : y ∈ translateSites (-(siteCenter t ℓ.site))
      (translateSites (siteCenter t ℓ.site)
        (typicalSplitFace t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) (dirOf ℓ, false) true)) ∨
      y ∈ translateSites (-(siteCenter t ℓ.site))
      (translateSites (siteCenter t ℓ.site)
        (typicalSplitFace t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) (dirOf ℓ, false) false)) := by
    obtain ⟨w, hw, rfl⟩ := (mem_translateSites_iff _ _ y).mp hy
    rcases Finset.mem_union.mp hw with h | h
    · left
      rw [← hsplit true]
      exact (mem_translateSites _ _ w).mpr (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2
    · right
      rw [← hsplit false]
      exact (mem_translateSites _ _ w).mpr (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2
  rcases hmem with h | h
  · exact splitFace_subset_negativeFaceCore (by omega) (dirOf ℓ) true (mem_translateSites_neg _ _ h)
  · exact splitFace_subset_negativeFaceCore (by omega) (dirOf ℓ) false (mem_translateSites_neg _ _ h)

end actual

end NearCritical.Section10
