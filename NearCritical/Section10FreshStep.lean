module

public import NearCritical.Section10ActualRoute
public import NearCritical.Section10UnconditionalStep

/-! A moving step of the actual layout reads no revealed bond.

* `NestLayout.readSet_disjoint_S₀`: abstract form, from three geometric facts
  (left tube meets no cube but the site's, right tube none but the target's,
  middle region meets no cube) and no exit points.
* `stepL_disjoint_cube_of_ne`, `stepR_disjoint_cube_of_ne`: the tube arithmetic
  on the coarse lattice `2t Z^d`.
* `actualLayout_readSet_disjoint`: the hypothesis `hfresh` of
  `NestLayout.moveSuccess_eq` / `moveSuccess_ge` for every label with a tube.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

section abstract
variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.readSet_disjoint_S₀ (F : Λ.Φ₀) (ℓ : RouteLabel D)
    (hLQ : ∀ j ∈ Λ.siteBox, j ≠ ℓ.site → Disjoint (Λ.L ℓ) (Λ.Q j))
    (hRQ : ∀ j ∈ Λ.siteBox, j ≠ ℓ.target → Disjoint (Λ.R ℓ) (Λ.Q j))
    (hMQ : ∀ j ∈ Λ.siteBox, Disjoint (Λ.Mid ℓ) (Λ.Q j))
    (hexit : Λ.exitPts ℓ = ∅) :
    Disjoint (Λ.readSet F ℓ) (Λ.S₀ F) := by
  rw [Finset.disjoint_left]
  intro e he heS
  unfold NestLayout.S₀ revealBondsOf at heS
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp heS
  unfold clusterFamilyRevealBonds at hb
  obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨hb1, _, _⟩ := (mem_clusterRevealBonds _ _ _).mp hbj
  unfold NestLayout.readSet stepReadSet at he
  rw [hexit] at he
  have hcrit : b ∈ sprinklingAvailableBonds (Λ.L ℓ) (Λ.Q ℓ.site) (Λ.Fat F ℓ.site) ∪
      sprinklingAvailableBonds (Λ.R ℓ) (Λ.Q ℓ.target) (Λ.Fat F ℓ.target) ∪
      internalBondSet (Λ.Mid ℓ) := by
    rcases Finset.mem_union.mp he with h | h
    · rcases Finset.mem_union.mp h with h1 | h1
      · obtain ⟨b', hb', hbb⟩ := Finset.mem_image.mp h1
        rw [← (Prod.mk.inj hbb).2]
        exact hb'
      · obtain ⟨b', _, hbb⟩ := Finset.mem_image.mp h1
        exact absurd (Prod.mk.inj hbb).1 (by simp)
    · simp [bothLayers] at h
  rcases Finset.mem_union.mp hcrit with h | h
  · rcases Finset.mem_union.mp h with h1 | h1
    · obtain ⟨hint, hnot⟩ := Finset.mem_sdiff.mp h1
      have hbL : b.1 ∈ Λ.L ℓ := ((mem_internalBondSet _ _).mp hint).1
      by_cases hjs : j = ℓ.site
      · subst hjs
        exact hnot hbj
      · exact Finset.disjoint_left.mp (hLQ j hj hjs) hbL hb1
    · obtain ⟨hint, hnot⟩ := Finset.mem_sdiff.mp h1
      have hbR : b.1 ∈ Λ.R ℓ := ((mem_internalBondSet _ _).mp hint).1
      by_cases hjs : j = ℓ.target
      · subst hjs
        exact hnot hbj
      · exact Finset.disjoint_left.mp (hRQ j hj hjs) hbR hb1
  · have hbM : b.1 ∈ Λ.Mid ℓ := ((mem_internalBondSet _ _).mp h).1
    exact Finset.disjoint_left.mp (hMQ j hj) hbM hb1

end abstract

/-! ### Tube arithmetic -/

lemma coarse_cast {d : ℕ} (t : ℕ) (a x : Vertex d) (k : Fin d) :
    ((x k - coarseCenter t a k : ℤ) : ℝ) = (x k : ℝ) - 2 * (t : ℝ) * (a k : ℝ) := by
  simp only [coarseCenter]
  push_cast
  ring

/-- Transverse coordinates: a tube point in a coarse cube forces equal coarse
coordinate. -/
lemma coarse_coord_eq_of_transverse {t : ℕ} (ht : 0 < t) {xk : ℝ} {ak bk : ℤ}
    (h1 : -3 * (t:ℝ) / 8 < xk - 2 * (t:ℝ) * (ak : ℝ))
    (h2 : xk - 2 * (t:ℝ) * (ak : ℝ) < 3 * (t:ℝ) / 8)
    (h3 : 2 * |xk - 2 * (t:ℝ) * (bk : ℝ)| < (t:ℝ)) : bk = ak := by
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have h4 := abs_lt.mp (by linarith : |xk - 2 * (t:ℝ) * (bk : ℝ)| < (t:ℝ) / 2)
  rcases lt_trichotomy bk ak with h | h | h
  · have : (bk : ℝ) + 1 ≤ (ak : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    nlinarith [h4.1, h4.2]
  · exact h
  · have : (ak : ℝ) + 1 ≤ (bk : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    nlinarith [h4.1, h4.2]

theorem stepL_disjoint_cube_of_ne {d t : ℕ} (ht : 0 < t) (a b : Vertex d) (i : Fin d)
    (hab : b ≠ a) :
    Disjoint (stepL t (coarseCenter t a) i) (typicalCube t (coarseCenter t b)) := by
  rw [Finset.disjoint_left]
  intro x hxL hxQ
  apply hab
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  obtain ⟨hlo, hhi, htr⟩ := (mem_stepTube t (coarseCenter t a) x i _ _ (by norm_num)
    (by norm_num)).mp hxL
  funext k
  have hq := typicalCube_coord hxQ k
  rw [coarse_cast] at hq
  by_cases hk : k = i
  · subst hk
    rw [coarse_cast] at hlo hhi
    have h4 := abs_lt.mp (by linarith : |(x k : ℝ) - 2 * (t:ℝ) * (b k : ℝ)| < (t:ℝ) / 2)
    rcases lt_trichotomy (b k) (a k) with h | h | h
    · have : (b k : ℝ) + 1 ≤ (a k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
      nlinarith [h4.1, h4.2]
    · exact h
    · have : (a k : ℝ) + 1 ≤ (b k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
      nlinarith [h4.1, h4.2]
  · have h := htr k hk
    rw [coarse_cast] at h
    exact coarse_coord_eq_of_transverse ht h.1 h.2 hq

theorem stepR_disjoint_cube_of_ne {d t : ℕ} (ht : 0 < t) (a b : Vertex d) (i : Fin d)
    (hab : b ≠ a + Pi.single i 1) :
    Disjoint (stepR t (coarseCenter t a) i) (typicalCube t (coarseCenter t b)) := by
  rw [Finset.disjoint_left]
  intro x hxR hxQ
  apply hab
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  obtain ⟨hlo, hhi, htr⟩ := (mem_stepTube t (coarseCenter t a) x i _ _ (by norm_num)
    (by norm_num)).mp hxR
  funext k
  have hq := typicalCube_coord hxQ k
  rw [coarse_cast] at hq
  by_cases hk : k = i
  · subst hk
    rw [coarse_cast] at hlo hhi
    simp only [Pi.add_apply, Pi.single_eq_same]
    have h4 := abs_lt.mp (by linarith : |(x k : ℝ) - 2 * (t:ℝ) * (b k : ℝ)| < (t:ℝ) / 2)
    rcases lt_trichotomy (b k) (a k + 1) with h | h | h
    · have : (b k : ℝ) + 1 ≤ (a k : ℝ) + 1 := by exact_mod_cast Int.add_one_le_iff.mpr h
      nlinarith [h4.1, h4.2]
    · exact h
    · have : (a k : ℝ) + 1 + 1 ≤ (b k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
      nlinarith [h4.1, h4.2]
  · have h := htr k hk
    rw [coarse_cast] at h
    simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
    exact coarse_coord_eq_of_transverse ht h.1 h.2 hq

lemma stepMid_subset_stepR {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    stepMid t c i ⊆ stepR t c i := by
  unfold stepMid stepR translateSites
  refine Finset.image_subset_image ?_
  rw [section9FiniteMiddle_eq_inter]
  exact Finset.inter_subset_right

/-! ### The actual layout -/

theorem actualLayout_readSet_disjoint (D : ℕ) (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t)
    (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ)
    (F : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Φ₀) (ℓ : RouteLabel D)
    (hℓ : ¬ ℓ.isExit) :
    Disjoint ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).readSet F ℓ)
      ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).S₀ F) := by
  have ht0 : 0 < t := by omega
  refine NestLayout.readSet_disjoint_S₀ _ F ℓ ?_ ?_ ?_ ?_
  · intro j _ hjs
    show Disjoint (LOf t M ℓ) (typicalCube t (siteCenter t j))
    unfold LOf
    by_cases h : HasTube M ℓ
    · rw [if_pos h]
      exact stepL_disjoint_cube_of_ne ht0 _ _ _ (fun he => hjs (vecSite_injective he))
    · rw [if_neg h]
      exact Finset.disjoint_empty_left _
  · intro j _ hjt
    show Disjoint (ROf t M ℓ) (typicalCube t (siteCenter t j))
    unfold ROf
    by_cases h : HasTube M ℓ
    · rw [if_pos h]
      refine stepR_disjoint_cube_of_ne ht0 _ _ _ (fun he => hjt (vecSite_injective ?_))
      rw [he, dirOf_spec h]
    · rw [if_neg h]
      exact Finset.disjoint_empty_left _
  · intro j _
    show Disjoint (MidOf t M ℓ) (typicalCube t (siteCenter t j))
    unfold MidOf
    by_cases h : HasTube M ℓ
    · rw [if_pos h]
      by_cases hjs : j = ℓ.site
      · rw [hjs]
        exact Finset.disjoint_of_subset_left (stepMid_subset_stepR _ _ _)
          (stepR_disjoint_near_cube t _ _)
      · exact Finset.disjoint_of_subset_left (stepMid_subset_stepL _ _ _)
          (stepL_disjoint_cube_of_ne ht0 _ _ _ (fun he => hjs (vecSite_injective he)))
    · rw [if_neg h]
      exact Finset.disjoint_empty_left _
  · unfold NestLayout.exitPts
    rw [if_neg (fun h => hℓ h.1)]

end NearCritical.Section10
