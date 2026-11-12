module
public import NearCritical.HomogenizedLogUpper
public import NearCritical.ConductivityUpperBound

/-! Full parameter-range source prop.upper_log, conditional only on named
STANDARD inputs. The supplied coefficient is identified by actual triadic
Dirichlet-mean convergence; it is not constructed or redefined here. -/
@[expose] public section
noncomputable section
namespace NearCritical

lemma triadic_limit_le_parameter {d : ℕ} (i : Fin d) {κ : ℝ → ℝ}
    (limitInput : TriadicDirichletLimitInput d i κ) (p : unitInterval)
    (hp : criticalPoint d < p) : κ (p:ℝ) ≤ (p:ℝ) := by
  have hU : (centeredBox d 0).Nonempty := ⟨0,mem_centeredBox.mpr (fun _ => by simp)⟩
  exact (triadic_limit_le_full_cube i limitInput p hp 0).trans
    (annealedFull_le_parameter _ hU i p)

/-- Literal ALL-parameter prop.upper_log deduction. No desired upper rate,
finite-cube domination, affine bound or boundary comparison is assumed. -/
theorem homogenized_global_log_upper_of_standard_inputs {d : ℕ} (i : Fin d) (κ : ℝ → ℝ)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (limitInput : TriadicDirichletLimitInput d i κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ p : unitInterval, criticalPoint d < p →
      κ (p:ℝ) ≤ D*((p:ℝ)-(criticalPoint d:ℝ))^3*
        |Real.log ((p:ℝ)-(criticalPoint d:ℝ))| := by
  obtain ⟨ε,D0,hε,hD0,hlocal⟩ := homogenized_log_upper_of_standard_inputs i κ
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic limitInput
  let L := -Real.log (1-(criticalPoint d:ℝ))
  have hL : 0 < L := by
    dsimp [L]
    exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  let B0 := 1/(ε^3*L)
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  refine ⟨max D0 B0,lt_of_lt_of_le hD0 (le_max_left _ _),?_⟩
  intro p hp
  let gap := (p:ℝ)-(criticalPoint d:ℝ)
  have hg : 0 < gap := sub_pos.mpr hp
  have hgapbound : gap ≤ 1-(criticalPoint d:ℝ) := by dsimp [gap]; linarith [p.2.2]
  change κ (p:ℝ) ≤ max D0 B0*gap^3*|Real.log gap|
  by_cases hs : gap ≤ ε
  · have h := hlocal gap hg hs
    have he : (criticalPoint d:ℝ)+gap = (p:ℝ) := by dsimp [gap]; ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hg.le _)) (abs_nonneg _))
  · have hsmall : ε ≤ gap := (le_of_not_ge hs)
    have hlog : L ≤ |Real.log gap| := by
      have h := Real.log_le_log hg hgapbound
      have ha := neg_le_abs (Real.log gap)
      dsimp [L]
      linarith
    have hden : 0 < ε^3*L := by positivity
    have hproduct : ε^3*L ≤ gap^3*|Real.log gap| :=
      mul_le_mul (pow_le_pow_left₀ hε.le hsmall 3) hlog hL.le (pow_nonneg hg.le _)
    have hunit : 1 ≤ B0*gap^3*|Real.log gap| := by
      calc
        1 ≤ (gap^3*|Real.log gap|)/(ε^3*L) := (le_div_iff₀ hden).mpr (by nlinarith)
        _ = _ := by dsimp [B0]; ring
    have hκ : κ (p:ℝ) ≤ 1 := (triadic_limit_le_parameter i limitInput p hp).trans p.2.2
    exact hκ.trans (hunit.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hg.le _)) (abs_nonneg _)))

end NearCritical
