module

public import NearCritical.Section10FreshStep
public import NearCritical.Section9DiameterTail

/-! The intrinsic-diameter failure probability of a lattice step.

* `NestLayout.diamFailure_le`: `diameter_tail_le` applied to the view of a step
  of an abstract layout (hypotheses: the middle region lies in the left tube
  and off the site cube; source and target patches at distance `>= n` from the
  pivot pairs).
* `face_dist_mid_L`, `face_dist_mid_R`: in the actual tube geometry the source
  face and the target face are at distance at least `t/8` from the middle
  region (the source's `|x - e_-|, |y - e_+| >~ n`, with the constant `1/8`).
* `actualLayout_diamFailure_le`: the bound for every label with a tube of the
  actual layout, at scale `n = t/8`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

section abstract
variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.diamFailure_le (hd : 5 ≤ d) {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hG : CriticalSupGreenUpper d G₀) (q : unitInterval) (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (hMidL : Λ.Mid ℓ ⊆ Λ.L ℓ)
    (hMidQ : Disjoint (Λ.Mid ℓ : Set (Vertex d)) (Λ.Q ℓ.site : Set (Vertex d)))
    {n : ℝ} (hn : 0 < n)
    (hA : ∀ e ∈ orientedLatticePairs (Λ.Mid ℓ),
      ∀ a ∈ sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2), n ≤ latticeDistance a e.1)
    (hB : ∀ e ∈ orientedLatticePairs (Λ.Mid ℓ),
      ∀ b ∈ sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ), n ≤ latticeDistance b e.2) :
    ((percolation d (criticalPoint d)).prod (percolation d q)).real
      {z | ¬ svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
        (Λ.tgt G ℓ) ≤ Λ.Kdiam} ≤
      (1 + ((orientedLatticePairs (Λ.Mid ℓ)).card : ℝ) *
        (((sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)).card : ℝ) *
          (((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) *
            (2 * (G₀^2 * greenConvConst d * n^((4 : ℝ)-(d : ℝ)) *
              (G₀ * n^((2 : ℝ)-(d : ℝ))) * (q : ℝ)))))) / ((Λ.Kdiam : ℝ) + 1) := by
  have hK : (0:ℝ) < (Λ.Kdiam : ℝ) + 1 := by positivity
  have h := diameter_tail_le hd hG0 hG q (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site)
    (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
    (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2))
    (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)) hMidL hMidQ hn hA hB hK
  refine (measureReal_mono (μ := (percolation d (criticalPoint d)).prod (percolation d q)) ?_
    (measure_ne_top _ _)).trans h
  intro z hz
  have hz' : Λ.Kdiam + 1 ≤ svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target)
      (Λ.src G ℓ x.2) (Λ.tgt G ℓ) := Nat.lt_of_not_le hz
  have hz'' := (Nat.cast_le (α := ℝ)).mpr hz'
  push_cast at hz''
  exact hz''

end abstract

/-! ### Distances in the actual tube geometry -/

lemma latticeDistance_ge_coord {d : ℕ} (x y : Vertex d) (i : Fin d) :
    |(x i : ℝ) - (y i : ℝ)| ≤ latticeDistance x y := by
  have h := dist_le_pi_dist (vertexReal x) (vertexReal y) i
  rw [Real.dist_eq] at h
  exact h

lemma halfSide_le {t : ℕ} : (((t - 1) / 2 : ℕ) : ℝ) ≤ (t : ℝ) / 2 := by
  have h : 2 * ((t - 1) / 2) ≤ t := by omega
  have h' : (2:ℝ) * (((t - 1) / 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  linarith

theorem face_dist_mid_L {d t : ℕ} (c : Vertex d) (i : Fin d) {x e : Vertex d}
    (hx : x ∈ typicalFace t c (i, true)) (he : e ∈ stepMid t c i) :
    (t : ℝ) / 8 ≤ latticeDistance x e := by
  have hxi : x i - c i = (((t - 1) / 2 : ℕ) : ℤ) := by
    have h := (Finset.mem_filter.mp hx).2
    simpa using h
  have heR := ((mem_stepTube t c e i _ _ (by norm_num) (by norm_num)).mp
    (stepMid_subset_stepR t c i he)).1
  have hxr : ((x i - c i : ℤ) : ℝ) ≤ (t : ℝ) / 2 := by
    rw [hxi]
    exact_mod_cast halfSide_le
  have h := latticeDistance_ge_coord x e i
  push_cast at heR hxr
  have h2 := neg_abs_le ((x i : ℝ) - (e i : ℝ))
  linarith

theorem face_dist_mid_R {d t : ℕ} (c : Vertex d) (i : Fin d) {y e : Vertex d}
    (hy : y ∈ typicalFace t (farCenter t c i) (i, false)) (he : e ∈ stepMid t c i) :
    (t : ℝ) / 8 ≤ latticeDistance y e := by
  have hyi : y i - farCenter t c i i = -(((t - 1) / 2 : ℕ) : ℤ) := by
    have h := (Finset.mem_filter.mp hy).2
    simpa using h
  rw [farCenter_apply_self] at hyi
  have heL := ((mem_stepTube t c e i _ _ (by norm_num) (by norm_num)).mp
    (stepMid_subset_stepL t c i he)).2.1
  have hyr : -((t : ℝ) / 2) ≤ ((y i - (c i + 2 * (t : ℤ)) : ℤ) : ℝ) := by
    rw [hyi, Int.cast_neg]
    have hh : ((((t - 1) / 2 : ℕ) : ℤ) : ℝ) ≤ (t : ℝ) / 2 := by exact_mod_cast halfSide_le
    linarith
  have h := latticeDistance_ge_coord y e i
  push_cast at heL hyr
  have h2 := le_abs_self ((y i : ℝ) - (e i : ℝ))
  linarith

lemma mem_typicalFace_of_patch {d : ℕ} {typ : TypicalParameters} {t : ℕ} {z : Vertex d}
    {ω : Configuration d} {C : Finset (Vertex d)} {face : Fin d × Bool} {pl : Bool}
    {x : Vertex d} (hx : x ∈ typicalRegularPatch typ t z ω C face pl) :
    x ∈ typicalFace t z face := by
  have h1 := (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  exact (Finset.mem_filter.mp h1).1

/-- **Diameter failure probability of a step of the actual layout.** -/
theorem actualLayout_diamFailure_le {D : ℕ} (hd : 5 ≤ D + 1) {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hG : CriticalSupGreenUpper (D + 1) G₀) (q : unitInterval)
    (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
    (MOff Mcoal Kdiam M : ℕ) (Λ : NestLayout D (D + 1))
    (hΛ : Λ = actualLayout D typ t ht k hk MOff Mcoal Kdiam M)
    (G : Λ.Φ) (ℓ : RouteLabel D) (hℓ : HasTube M ℓ) (x : Λ.X) :
    ((percolation (D + 1) (criticalPoint (D + 1))).prod (percolation (D + 1) q)).real
      {z | ¬ svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
        (Λ.tgt G ℓ) ≤ Λ.Kdiam} ≤
      (1 + ((orientedLatticePairs (Λ.Mid ℓ)).card : ℝ) *
        (((sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)).card : ℝ) *
          (((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) *
            (2 * (G₀^2 * greenConvConst (D + 1) * ((t : ℝ) / 8)^((4 : ℝ)-((D + 1 : ℕ) : ℝ)) *
              (G₀ * ((t : ℝ) / 8)^((2 : ℝ)-((D + 1 : ℕ) : ℝ))) * (q : ℝ)))))) /
        ((Λ.Kdiam : ℝ) + 1) := by
  subst hΛ
  have htR : (0:ℝ) < (t : ℝ) / 8 := by
    have : (0:ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    linarith
  have hMid : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Mid ℓ =
      stepMid t (siteCenter t ℓ.site) (dirOf ℓ) := by
    show MidOf t M ℓ = _
    unfold MidOf
    rw [if_pos hℓ]
  have hL : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).L ℓ =
      stepL t (siteCenter t ℓ.site) (dirOf ℓ) := by
    show LOf t M ℓ = _
    unfold LOf
    rw [if_pos hℓ]
  refine NestLayout.diamFailure_le _ hd hG0 hG q G ℓ x ?_ ?_ htR ?_ ?_
  · rw [hMid, hL]
    exact stepMid_subset_stepL _ _ _
  · rw [hMid]
    have h := Finset.disjoint_of_subset_left (stepMid_subset_stepR t (siteCenter t ℓ.site)
      (dirOf ℓ)) (stepR_disjoint_near_cube t (siteCenter t ℓ.site) (dirOf ℓ))
    exact Finset.disjoint_coe.mpr h
  · intro e he a ha
    rw [hMid] at he
    obtain ⟨he1, _, _⟩ := (mem_orientedLatticePairs _ e.1 e.2).mp he
    unfold sprinklingTargetBoundary at ha
    obtain ⟨C, _, haC⟩ := Finset.mem_biUnion.mp ha
    exact face_dist_mid_L _ _ (mem_typicalFace_of_patch haC) he1
  · intro e he b hb
    rw [hMid] at he
    obtain ⟨_, he2, _⟩ := (mem_orientedLatticePairs _ e.1 e.2).mp he
    unfold sprinklingTargetBoundary at hb
    obtain ⟨C, _, hbC⟩ := Finset.mem_biUnion.mp hb
    have hface : b ∈ typicalFace t (siteCenter t ℓ.target) (dirOf ℓ, false) := by
      rcases Finset.mem_union.mp hbC with h | h
      · exact mem_typicalFace_of_patch h
      · exact mem_typicalFace_of_patch h
    rw [siteCenter_target t hℓ] at hface
    exact face_dist_mid_R _ _ hface he2

end NearCritical.Section10
