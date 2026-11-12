module

public import NearCritical.SplitCrossPlacementMoment

/-! The number of free interior positions cancels the dimension-dependent
part of the tube decay. Each non-face edge contributes two powers of scale
after its endpoint is summed. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode
open scoped Classical BigOperators

private def crossingEdgeEquiv (d : ℕ) :
    CrossingEdgeIndex d ≃ CrossingBranch (4 * d) ⊕ InteriorIndex d ⊕ Fin (4 * d) where
  toFun v := match h : v.val with
    | root => (v.property h).elim
    | spine k => .inl ⟨spine k, rfl⟩
    | entry k => .inl ⟨entry k, rfl⟩
    | exterior k => .inl ⟨exterior k, rfl⟩
    | cubeDummy k => .inr (.inl (k, false))
    | exteriorDummy k => .inr (.inl (k, true))
    | face k => .inr (.inr k)
  invFun s := match s with
    | .inl v => ⟨v.val, by
        intro h
        have hv := v.property
        rw [h] at hv
        cases hv⟩
    | .inr (.inl i) => ⟨interiorNode i, by rcases i with ⟨k, b⟩; cases b <;> simp [interiorNode]⟩
    | .inr (.inr k) => ⟨face k, by simp⟩
  left_inv := by
    rintro ⟨v, hv⟩
    cases v <;> first | rfl | exact (hv rfl).elim
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨k, b⟩ | k)
    · cases v <;> first | rfl | cases hv
    · cases b <;> rfl
    · rfl

theorem crossingSummedScale_product {d t : ℕ} :
    ((crossingEdgeIndices d).map (fun v => crossingSummedScale d t v.val)).prod =
      ((t : ℝ) ^ ((2 : ℝ) - (d : ℝ))) ^
        (Fintype.card (CrossingBranch (4 * d)) + Fintype.card (InteriorIndex d)) := by
  have hset : (crossingEdgeIndices d).toFinset = Finset.univ := by
    ext i
    simp [mem_crossingEdgeIndices]
  rw [← List.prod_toFinset _ (crossingEdgeIndices_nodup d), hset]
  let m := (t : ℝ) ^ ((2 : ℝ) - (d : ℝ))
  let s : CrossingBranch (4 * d) ⊕ InteriorIndex d ⊕ Fin (4 * d) → ℝ
    | .inl _ | .inr (.inl _) => m
    | .inr (.inr _) => 1
  calc
    _ = ∏ i, s i := by
      symm
      apply Fintype.prod_equiv (crossingEdgeEquiv d).symm s _
      rintro (⟨v, hv⟩ | ⟨k, b⟩ | k)
      · cases v <;> first | rfl | cases hv
      · cases b <;> rfl
      · rfl
    _ = _ := by
      simp only [Fintype.prod_sum_type, s, Finset.prod_const, Finset.card_univ, one_pow, mul_one]
      rw [← pow_add]

private theorem volume_base_lower {d t : ℕ} (hd : 1 ≤ d) :
    let M : ℕ := 2048 * d
    (t : ℝ) / (M : ℝ) ≤ (2 * (spineRadius (4 * d - 1) t / 2) + 1 : ℕ) ∧
    (t : ℝ) / (M : ℝ) ≤ (2 * (t / 2048) + 1 : ℕ) ∧
    (t : ℝ) / (M : ℝ) ≤ (2 * legBoxRadius t + 1 : ℕ) := by
  intro M
  have hm : 0 < M := by dsimp [M]; omega
  have hm' : (0 : ℝ) < M := by exact_mod_cast hm
  have hdiv (D : ℕ) (hD : 0 < D) (hDM : D ≤ M) :
      (t : ℝ) / (M : ℝ) ≤ (2 * (t / D) + 1 : ℕ) := by
    apply (div_le_iff₀ hm').mpr
    exact_mod_cast (show t ≤ (2 * (t / D) + 1) * M from
      (show t ≤ (2 * (t / D) + 1) * D by
        calc
          t ≤ (t / D + 1) * D :=
            ((Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_succ_self (t / D))).le
          _ ≤ _ := Nat.mul_le_mul_right D (by omega : t / D + 1 ≤ 2 * (t / D) + 1)
      ).trans (Nat.mul_le_mul_left _ hDM))
  have hD : 256 * (4 * d - 1 + 1) * 2 = M := by dsimp [M]; omega
  constructor
  · simpa only [spineRadius, Nat.div_div_eq_div_mul, hD] using hdiv M hm le_rfl
  · exact ⟨hdiv 2048 (by omega) (by dsimp [M]; omega),
      hdiv 64 (by omega) (by dsimp [M]; omega)⟩

private theorem placement_volume_lower {d t : ℕ} (hd : 1 ≤ d)
    (x : Vertex d) (axis : Fin d) (v : SplitTreeNode (4 * d))
    (hroot : v ≠ root) (hface : ∀ k, v ≠ face k) :
    ((t : ℝ) / (2048 * (d : ℝ))) ^ d ≤ ((nodeSites t x axis v).card : ℝ) := by
  obtain ⟨hs, hb, hi⟩ := volume_base_lower (t := t) hd
  push_cast at hs hb hi
  have hcard := nodeSiteCount_le_card t x axis v
  have hnon : 0 ≤ (t : ℝ) / (2048 * (d : ℝ)) := by positivity
  cases v with
  | root => exact (hroot rfl).elim
  | face k => exact (hface k rfl).elim
  | spine k =>
    exact (pow_le_pow_left₀ hnon hs d).trans (by exact_mod_cast hcard)
  | entry k | exterior k =>
    exact (pow_le_pow_left₀ hnon hb d).trans (by exact_mod_cast hcard)
  | cubeDummy k | exteriorDummy k =>
    exact (pow_le_pow_left₀ hnon hi d).trans (by exact_mod_cast hcard)


/-- Every branch or interior terminal contributes its placement volume
and one interior edge probability. -/
theorem crossing_placement_scale_lower {d t : ℕ} (hd : 1 ≤ d) (ht : 0 < t)
    (x : Vertex d) (axis : Fin d) :
    let n := Fintype.card (CrossingBranch (4 * d)) + Fintype.card (InteriorIndex d)
    ((2048 * (d : ℝ))⁻¹ ^ d) ^ n * (t : ℝ) ^ (2 * n) ≤
      ((branchPlacements t x axis).card : ℝ) * ((interiorPlacements t x axis).card : ℝ) *
        ((crossingEdgeIndices d).map (fun v => crossingSummedScale d t v.val)).prod := by
  intro n
  let M := 2048 * (d : ℝ)
  let V := ((t : ℝ) / M) ^ d
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hM : 0 < M := by dsimp [M]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hbranch : V ^ Fintype.card (CrossingBranch (4 * d)) ≤
      ((branchPlacements t x axis).card : ℝ) := by
    rw [branchPlacements, Fintype.card_piFinset, Nat.cast_prod, ← Finset.card_univ, ← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ => hV)
    intro v _
    obtain ⟨v, hv⟩ := v
    cases v with
    | spine _ | entry _ | exterior _ => exact placement_volume_lower hd x axis _ (by simp) (by simp)
    | root | cubeDummy _ | exteriorDummy _ | face _ => cases hv
  have hinterior : V ^ Fintype.card (InteriorIndex d) ≤ ((interiorPlacements t x axis).card : ℝ) := by
    rw [interiorPlacements, Fintype.card_piFinset, Nat.cast_prod, ← Finset.card_univ, ← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ => hV)
    rintro ⟨k, b⟩ _
    cases b <;> exact placement_volume_lower hd x axis _ (by simp [interiorNode]) (by simp [interiorNode])
  have htube : V * (t : ℝ) ^ ((2 : ℝ) - (d : ℝ)) = M⁻¹ ^ d * (t : ℝ) ^ 2 := by
    unfold V
    rw [div_eq_mul_inv, mul_pow, mul_comm ((t : ℝ) ^ d), mul_assoc, ← Real.rpow_natCast (t : ℝ) d,
      ← Real.rpow_add ht']
    congr 1
    have hexp : (d : ℝ) + (2 - (d : ℝ)) = 2 := by ring
    rw [hexp, Real.rpow_two]
  change (M⁻¹ ^ d) ^ n * (t : ℝ) ^ (2 * n) ≤ _
  rw [pow_mul, ← mul_pow, ← htube, mul_pow, crossingSummedScale_product]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp only [n]
  rw [pow_add]
  exact mul_le_mul hbranch hinterior (pow_nonneg hV _) (by positivity)


theorem crossingBranch_card (L : ℕ) :
    Fintype.card (CrossingBranch L) = (L - 1) + L + L := by
  let e : CrossingBranch L ≃ Fin (L - 1) ⊕ Fin L ⊕ Fin L := {
    toFun := fun v => match h : v.val with
      | spine k => .inl k
      | entry k => .inr (.inl k)
      | exterior k => .inr (.inr k)
      | root | cubeDummy _ | exteriorDummy _ | face _ => by
        have hv := v.property
        rw [h] at hv
        cases hv
    invFun := fun s => match s with
      | .inl k => ⟨spine k, rfl⟩
      | .inr (.inl k) => ⟨entry k, rfl⟩
      | .inr (.inr k) => ⟨exterior k, rfl⟩
    left_inv := by
      rintro ⟨v, hv⟩
      cases v <;> first | rfl | cases hv
    right_inv := by rintro (k | k | k) <;> rfl }
  rw [Fintype.card_congr e]
  simp [Nat.add_assoc]

theorem crossingInteriorPlacement_card_index (d : ℕ) :
    Fintype.card (CrossingBranch (4 * d)) + Fintype.card (InteriorIndex d) = 20 * d - 1 := by
  simp only [crossingBranch_card, InteriorIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

end NearCritical.SplitCrossDirect
