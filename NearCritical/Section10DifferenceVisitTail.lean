module

public import NearCritical.Section10DifferenceVisitCount

/-! Split a finite difference history at its successive visit times. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

theorem differenceVisitCount_append {D n m : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (a : DifferenceHistory D n) (b : DifferenceHistory D m) :
    differenceVisitCount B x (Fin.append a b) =
      differenceVisitCount B x a +
        differenceVisitCount B (x + differenceDisplacement a n) b := by
  classical
  unfold differenceVisitCount
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [differenceDisplacement_append_left a b (Finset.mem_range.mp hj).le]
  · apply Finset.sum_congr rfl
    intro j _
    rw [differenceDisplacement_append_right, add_assoc]

/-- The number of visits strictly before time t. -/
def differenceVisitsBefore {D T : ℕ} (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ)
    (h : DifferenceHistory D T) (t : ℕ) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range t, if x + differenceDisplacement h j ∈ B then 1 else 0

/-- Time t is the kth visit, using one-based visit indices. -/
def differenceIndexedVisit {D T : ℕ} (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ)
    (h : DifferenceHistory D T) (k t : ℕ) : Prop :=
  x + differenceDisplacement h t ∈ B ∧ differenceVisitsBefore B x h t + 1 = k

private theorem visitsBefore_succ {D T : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (h : DifferenceHistory D T) (t : ℕ) :
    differenceVisitsBefore B x h (t+1) =
      differenceVisitsBefore B x h t +
        (if x + differenceDisplacement h t ∈ B then 1 else 0) := by
  classical
  exact Finset.sum_range_succ _ _

theorem differenceIndexedVisit_exists {D T k : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (h : DifferenceHistory D T) (hk : 0 < k) :
    k ≤ differenceVisitCount B x h ↔ ∃ t < T, differenceIndexedVisit B x h k t := by
  classical
  have haux (N : ℕ) :
      k ≤ differenceVisitsBefore B x h N ↔ ∃ t < N, differenceIndexedVisit B x h k t := by
    induction N with
    | zero => simp [differenceVisitsBefore, Nat.not_le_of_gt hk]
    | succ N ih =>
      rw [visitsBefore_succ]
      by_cases hv : x + differenceDisplacement h N ∈ B
      · rw [if_pos hv]
        constructor
        · intro hle
          by_cases hprev : k ≤ differenceVisitsBefore B x h N
          · obtain ⟨t,ht,hh⟩ := ih.mp hprev
            exact ⟨t, by omega, hh⟩
          · exact ⟨N, by omega, hv, by omega⟩
        · rintro ⟨t,ht,hh⟩
          by_cases hlt : t < N
          · have hp := ih.mpr ⟨t,hlt,hh⟩
            omega
          · have heq : t = N := by omega
            subst t
            have := hh.2
            omega
      · rw [if_neg hv, add_zero]
        constructor
        · intro hle
          obtain ⟨t,ht,hh⟩ := ih.mp hle
          exact ⟨t, by omega, hh⟩
        · rintro ⟨t,ht,hh⟩
          apply ih.mpr
          refine ⟨t, ?_, hh⟩
          by_contra hlt
          have heq : t = N := by omega
          exact hv (heq ▸ hh.1)
  exact haux T


theorem differenceIndexedVisit_unique {D T k s t : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (h : DifferenceHistory D T)
    (hs : differenceIndexedVisit B x h k s) (ht : differenceIndexedVisit B x h k t) :
    s = t := by
  classical
  have hmono : Monotone (differenceVisitsBefore B x h) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [visitsBefore_succ]
    omega
  rcases lt_trichotomy s t with hlt | heq | hlt
  · have hm := hmono (show s+1 ≤ t by omega)
    rw [visitsBefore_succ, if_pos hs.1] at hm
    have h₁ := hs.2
    have h₂ := ht.2
    omega
  · exact heq
  · have hm := hmono (show t+1 ≤ s by omega)
    rw [visitsBefore_succ, if_pos ht.1] at hm
    have h₁ := hs.2
    have h₂ := ht.2
    omega

/-- The visit index is decided by the prefix. Once it is k, the suffix
needs K+1 visits to reach k+K because its time zero is the splitting visit. -/
theorem differenceIndexedVisit_append_tail {D n m k K : ℕ}
    (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ)
    (a : DifferenceHistory D n) (b : DifferenceHistory D m) :
    (differenceIndexedVisit B x (Fin.append a b) k n ∧
      k+K ≤ differenceVisitCount B x (Fin.append a b)) ↔
    (differenceIndexedVisit B x a k n ∧
      K+1 ≤ differenceVisitCount B (x + differenceDisplacement a n) b) := by
  classical
  have hp : differenceIndexedVisit B x (Fin.append a b) k n ↔
      differenceIndexedVisit B x a k n := by
    have hc : differenceVisitsBefore B x (Fin.append a b) n =
        differenceVisitsBefore B x a n := by
      unfold differenceVisitsBefore
      apply Finset.sum_congr rfl
      intro j hj
      rw [differenceDisplacement_append_left a b (Finset.mem_range.mp hj).le]
    unfold differenceIndexedVisit
    rw [hc, differenceDisplacement_append_left a b le_rfl]
  rw [hp, differenceVisitCount_append]
  constructor
  · rintro ⟨hh,hcount⟩
    have hindex : differenceVisitCount B x a + 1 = k := hh.2
    exact ⟨hh, by omega⟩
  · rintro ⟨hh,hcount⟩
    have hindex : differenceVisitCount B x a + 1 = k := hh.2
    exact ⟨hh, by omega⟩

private theorem indexedVisit_partition {D T k : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (hk : 0 < k) (P : DifferenceHistory D T → Prop) :
    differenceEventMass D T (fun h => k ≤ differenceVisitCount B x h ∧ P h) =
      ∑ t ∈ Finset.range T, differenceEventMass D T
        (fun h => differenceIndexedVisit B x h k t ∧ P h) := by
  classical
  unfold differenceEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hp : P h
  · simp only [hp, and_true]
    by_cases hn : k ≤ differenceVisitCount B x h
    · obtain ⟨t,ht,hvisit⟩ := (differenceIndexedVisit_exists B x h hk).mp hn
      rw [if_pos hn, Finset.sum_eq_single t, if_pos hvisit]
      · intro s _ hst
        exact if_neg (fun hs => hst (differenceIndexedVisit_unique B x h hs hvisit))
      · exact fun hnot => (hnot (Finset.mem_range.mpr ht)).elim
    · rw [if_neg hn]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      exact if_neg (fun hv => hn ((differenceIndexedVisit_exists B x h hk).mpr
        ⟨t, Finset.mem_range.mp ht, hv⟩))
  · simp [hp]

private theorem indexedVisit_restart_le {D T k K t : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (hD : 0 < D) (ht : t ≤ T)
    (hc : ∀ (m : ℕ) (y : Fin D → ℤ), differenceEventMass D m
      (fun b => K+1 ≤ differenceVisitCount B y b) ≤ 1/2) :
    differenceEventMass D T (fun h =>
      differenceIndexedVisit B x h k t ∧ k+K ≤ differenceVisitCount B x h) ≤
      (1/2) * differenceEventMass D T (fun h => differenceIndexedVisit B x h k t) := by
  classical
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le ht
  have hl (h : DifferenceHistory D (t+m)) :=
    differenceIndexedVisit_append_tail (k := k) (K := K) B x
      (fun i => h (Fin.castAdd m i)) (fun j => h (Fin.natAdd t j))
  have hp (h : DifferenceHistory D (t+m)) :
      differenceIndexedVisit B x h k t ↔
        differenceIndexedVisit B x (fun i => h (Fin.castAdd m i)) k t := by
    have hd (j : ℕ) (hj : j ≤ t) : differenceDisplacement h j =
        differenceDisplacement (fun i => h (Fin.castAdd m i)) j := by
      simpa only [Fin.append_castAdd_natAdd] using
        (differenceDisplacement_append_left (fun i => h (Fin.castAdd m i))
          (fun j => h (Fin.natAdd t j)) hj)
    have hs : differenceVisitsBefore B x h t =
        differenceVisitsBefore B x (fun i => h (Fin.castAdd m i)) t := by
      unfold differenceVisitsBefore
      apply Finset.sum_congr rfl
      intro j hj
      rw [hd j (Finset.mem_range.mp hj).le]
    unfold differenceIndexedVisit
    rw [hs, hd t le_rfl]
  have hjoint (h : DifferenceHistory D (t+m)) :
      (differenceIndexedVisit B x h k t ∧ k+K ≤ differenceVisitCount B x h) ↔
      (differenceIndexedVisit B x (fun i => h (Fin.castAdd m i)) k t ∧
        K+1 ≤ differenceVisitCount B
          (x + differenceDisplacement (fun i => h (Fin.castAdd m i)) t)
          (fun j => h (Fin.natAdd t j))) := by
    simpa only [Fin.append_castAdd_natAdd] using hl h
  let P := fun a : DifferenceHistory D t => differenceIndexedVisit B x a k t
  have htotal : differenceEventMass D m (fun _ => True) = 1 := by
    simpa only [differenceEventMass, if_true] using differenceHistoryWeight_sum hD m
  have hmarg := differenceEventMass_restart (m := m) x P (fun _ _ => True)
  simp only [and_true, htotal, mul_one] at hmarg
  simp_rw [hjoint, hp]
  change differenceEventMass D (t+m) (fun h => P (fun i => h (Fin.castAdd m i)) ∧ _) ≤
    (1/2) * differenceEventMass D (t+m) (fun h => P (fun i => h (Fin.castAdd m i)))
  rw [differenceEventMass_restart x P (fun y b => K+1 ≤ differenceVisitCount B y b),
    hmarg, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P a
  · simp only [ha, if_true]
    rw [mul_comm (1/2 : ℝ)]
    apply mul_le_mul_of_nonneg_left (hc m _)
    unfold differenceHistoryWeight
    apply Finset.prod_nonneg
    intro i _
    obtain ⟨c,d⟩ := a i
    cases c <;> cases d <;> simp only [differenceStepWeight,lazyCoordinateWeight] <;> positivity
  · simp [ha]

/-- The block recurrence holds for the actual finite-history tail. -/
theorem differenceVisitCount_tail_step {D T k K : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (hD : 0 < D) (hk : 0 < k)
    (hc : ∀ (m : ℕ) (y : Fin D → ℤ), differenceEventMass D m
      (fun b => K+1 ≤ differenceVisitCount B y b) ≤ 1/2) :
    differenceEventMass D T (fun h => k+K ≤ differenceVisitCount B x h) ≤
      (1/2) * differenceEventMass D T (fun h => k ≤ differenceVisitCount B x h) := by
  have hleft (h : DifferenceHistory D T) :
      (k ≤ differenceVisitCount B x h ∧ k+K ≤ differenceVisitCount B x h) ↔
        k+K ≤ differenceVisitCount B x h := ⟨And.right, fun hh => ⟨by omega,hh⟩⟩
  have h1 := indexedVisit_partition B x hk (fun h : DifferenceHistory D T =>
    k+K ≤ differenceVisitCount B x h)
  have h2 := indexedVisit_partition B x (T := T) hk (fun _ => True)
  simp only [hleft] at h1
  simp only [and_true] at h2
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun t ht =>
    indexedVisit_restart_le B x hD (Finset.mem_range.mp ht).le hc)

/-- Each additional block halves the finite-history tail, preserving the
actual mass of the event that at least one visit occurs. -/
theorem differenceVisitCount_tail_with_first_hit {D : ℕ} (hD : 3 ≤ D)
    (B : Finset (Fin D → ℤ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (T l : ℕ) (x : Fin D → ℤ),
      differenceEventMass D T (fun h => l*K+1 ≤ differenceVisitCount B x h) ≤
        (1/2 : ℝ)^l * differenceEventMass D T (fun h => 1 ≤ differenceVisitCount B x h) := by
  obtain ⟨K,hK,hc⟩ := differenceVisitCount_block_contraction hD B
  refine ⟨K,hK,?_⟩
  intro T l x
  induction l with
  | zero => simp
  | succ l ih =>
    have hidx : (l+1)*K+1 = (l*K+1)+K := by ring
    rw [hidx]
    calc
      _ ≤ (1/2) * differenceEventMass D T (fun h => l*K+1 ≤ differenceVisitCount B x h) :=
        differenceVisitCount_tail_step B x (by omega) (by omega) hc
      _ ≤ (1/2 : ℝ) * ((1/2 : ℝ)^l *
          differenceEventMass D T (fun h => 1 ≤ differenceVisitCount B x h)) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

end NearCritical.Section10
