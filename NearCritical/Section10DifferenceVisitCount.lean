module

public import NearCritical.Section10DifferenceOccupation
public import NearCritical.Section10DifferenceRestart

/-! Finite-history visit expectation and the corrected block contraction.
The contraction follows from the actual uniform occupation bound and
Markov's inequality, with the hit visit included at continuation time zero. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

private lemma symbolWeight_nonneg (D : ℕ) (a : DifferenceSymbol D) :
    0 ≤ differenceStepWeight D a := by
  obtain ⟨a,b⟩ := a
  cases a <;> cases b <;> simp only [differenceStepWeight,lazyCoordinateWeight] <;> positivity

private lemma historyWeight_nonneg_visits {D T : ℕ} (h : DifferenceHistory D T) :
    0 ≤ differenceHistoryWeight h :=
  Finset.prod_nonneg fun _ _ => symbolWeight_nonneg _ _

/-- The actual finite product weights are normalized in positive dimension. -/
theorem differenceHistoryWeight_sum {D : ℕ} (hD : 0 < D) (T : ℕ) :
    (∑ h : DifferenceHistory D T, differenceHistoryWeight h) = 1 := by
  classical
  have hsingle : ∑ a, lazyCoordinateWeight D a = 1 := by
    rw [Fintype.sum_option]
    simp only [lazyCoordinateWeight, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp [hd] <;> ring
  have hpair : ∑ a, differenceStepWeight D a = 1 := by
    unfold differenceStepWeight
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hsingle, mul_one]
  unfold differenceHistoryWeight
  rw [← Fintype.prod_sum (fun (_ : Fin T) a => differenceStepWeight D a)]
  simp only [hpair, Finset.prod_const_one]

/-- Visit count over times 0 through T−1, including the start. -/
def differenceVisitCount {D T : ℕ} (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ)
    (h : DifferenceHistory D T) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range T, if x + differenceDisplacement h j ∈ B then 1 else 0

private theorem differenceEventMass_time_marginal {D T j : ℕ} (hD : 0 < D)
    (hj : j ≤ T) (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ) :
    differenceEventMass D T (fun h => x + differenceDisplacement h j ∈ B) =
      differenceEventMass D j (fun h => x + differenceDisplacement h j ∈ B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hl (h : DifferenceHistory D (j+m)) :
      differenceDisplacement h j = differenceDisplacement (fun i => h (Fin.castAdd m i)) j := by
    have h' := differenceDisplacement_append_left (fun i => h (Fin.castAdd m i))
      (fun k => h (Fin.natAdd j k)) (j := j) le_rfl
    simpa only [Fin.append_castAdd_natAdd] using h'
  simp_rw [hl]
  have hre := differenceEventMass_restart (m := m) x
    (fun a : DifferenceHistory D j => x + differenceDisplacement a j ∈ B)
    (fun _ _ => True)
  have hs : differenceEventMass D m (fun _ => True) = 1 := by
    simpa only [differenceEventMass, if_true] using differenceHistoryWeight_sum hD m
  simp only [and_true, hs, mul_one] at hre
  refine Eq.trans ?_ (hre.trans ?_)
  all_goals
    unfold differenceEventMass
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> rfl

private theorem differenceEventMass_terminal_mem {D j : ℕ}
    (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ) :
    differenceEventMass D j (fun h => x + differenceDisplacement h j ∈ B) =
      ∑ y ∈ B, differenceHistoryMass D j (y-x) := by
  classical
  unfold differenceEventMass differenceHistoryMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hdisp : differenceDisplacement h j = ∑ t, differenceStep D (h t) := by
    simp [differenceDisplacement, Fin.isLt]
  have he (y : Fin D → ℤ) : (∑ t, differenceStep D (h t)) = y-x ↔
      y = x + differenceDisplacement h j := by
    rw [← hdisp, eq_sub_iff_add_eq, add_comm (differenceDisplacement h j), eq_comm]
  simp_rw [he]
  by_cases hy : x + differenceDisplacement h j ∈ B
  · rw [if_pos hy]
    symm
    calc
      _ = (∏ t, differenceStepWeight D (h t)) := by
        rw [Finset.sum_eq_single (x + differenceDisplacement h j)]
        · simp
        · intro y _ hy'
          simp [hy']
        · exact fun hnot => (hnot hy).elim
      _ = _ := rfl
  · rw [if_neg hy]
    symm
    apply Finset.sum_eq_zero
    intro y hy'
    have hn : y ≠ x + differenceDisplacement h j := fun heq => hy (by simpa only [← heq] using hy')
    simp [hn]

/-- The uniform occupation bound gives a uniform expected number of
visits to a finite set, for every starting point and every horizon. -/
theorem differenceVisitCount_uniform_expectation {D : ℕ} (hD : 3 ≤ D)
    (B : Finset (Fin D → ℤ)) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (T : ℕ) (x : Fin D → ℤ),
      (∑ h : DifferenceHistory D T, differenceHistoryWeight h *
        (differenceVisitCount B x h : ℝ)) ≤ V := by
  classical
  obtain ⟨G,hG,hocc⟩ := differenceHistory_uniform_occupation hD
  refine ⟨(B.card : ℝ)*G, mul_nonneg (by positivity) hG, ?_⟩
  intro T x
  have hD' : 0 < D := by omega
  calc
    _ = ∑ j ∈ Finset.range T, differenceEventMass D T
        (fun h => x + differenceDisplacement h j ∈ B) := by
      simp_rw [differenceVisitCount, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      unfold differenceEventMass
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : x + differenceDisplacement h j ∈ B <;> simp [hh]
    _ = ∑ j ∈ Finset.range T, ∑ y ∈ B, differenceHistoryMass D j (y-x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [differenceEventMass_time_marginal hD' (Finset.mem_range.mp hj).le,
        differenceEventMass_terminal_mem]
    _ = ∑ y ∈ B, ∑ j ∈ Finset.range T, differenceHistoryMass D j (y-x) :=
      Finset.sum_comm
    _ ≤ ∑ _y ∈ B, G := Finset.sum_le_sum (fun y _ => hocc T (y-x))
    _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]

/-- Uniform block contraction. It is harmless to require K+1 visits
because the count includes continuation time zero. -/
theorem differenceVisitCount_block_contraction {D : ℕ} (hD : 3 ≤ D)
    (B : Finset (Fin D → ℤ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (T : ℕ) (x : Fin D → ℤ),
      differenceEventMass D T (fun h => K+1 ≤ differenceVisitCount B x h) ≤ 1/2 := by
  classical
  obtain ⟨V,hV,hbound⟩ := differenceVisitCount_uniform_expectation hD B
  obtain ⟨K,hK⟩ := exists_nat_gt (2*V)
  have hKpR : 0 < (K : ℝ) := by linarith
  have hKp : 0 < K := by exact_mod_cast hKpR
  refine ⟨K,hKp,?_⟩
  intro T x
  have hmarkov : (K : ℝ) *
      differenceEventMass D T (fun h => K+1 ≤ differenceVisitCount B x h) ≤ V := by
    refine le_trans ?_ (hbound T x)
    unfold differenceEventMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    by_cases hh : K+1 ≤ differenceVisitCount B x h
    · rw [if_pos hh, mul_comm (K : ℝ)]
      apply mul_le_mul_of_nonneg_left _ (historyWeight_nonneg_visits h)
      exact_mod_cast (show K ≤ differenceVisitCount B x h by omega)
    · rw [if_neg hh, mul_zero]
      exact mul_nonneg (historyWeight_nonneg_visits h) (by positivity)
  have hquot :
      differenceEventMass D T (fun h => K+1 ≤ differenceVisitCount B x h) ≤ V/(K : ℝ) :=
    (le_div_iff₀ hKpR).mpr (by simpa only [mul_comm] using hmarkov)
  exact hquot.trans ((div_le_iff₀ hKpR).mpr (by linarith))

/-- The first-hit factor is retained when restarting with one additional
block of K visits. The time-zero visit in the continuation is the hit. -/
theorem differenceFirstHit_block_contraction {D : ℕ} (hD : 3 ≤ D)
    (B : Finset (Fin D → ℤ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n m : ℕ) (x : Fin D → ℤ),
      differenceEventMass D (n+m) (fun h => differenceFirstHit B x h n ∧
        K+1 ≤ differenceVisitCount B
          (x + differenceDisplacement (fun i => h (Fin.castAdd m i)) n)
          (fun j => h (Fin.natAdd n j))) ≤
        (1/2) * differenceEventMass D n (fun h => differenceFirstHit B x h n) := by
  obtain ⟨K,hK,hcon⟩ := differenceVisitCount_block_contraction hD B
  exact ⟨K,hK,fun _ m x =>
    differenceFirstHit_restart_le B x (fun y h => K+1 ≤ differenceVisitCount B y h)
      (1/2) (fun y _ => hcon m y)⟩

end NearCritical.Section10
