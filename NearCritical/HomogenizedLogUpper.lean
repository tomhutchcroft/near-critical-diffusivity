module
public import NearCritical.TriadicDirichletLimit
public import NearCritical.IsotropicFiniteLogUpper

/-! Source prop.upper_log deduction for a supplied coefficient identified by
the named STANDARD actual triadic Dirichlet-limit input. Neither that input
nor its random-walk interpretation is constructed here; no new κ is defined. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Conditional source prop.upper_log. Every NEW finite-volume, boundary,
scale-selection and order-passage step is proved. Only named STANDARD arm,
entropic, pc-nontriviality and literal actual-cube triadic-limit inputs remain.
No upper-rate or cube-domination conclusion is part of the limit input. -/
theorem homogenized_log_upper_of_standard_inputs {d : ℕ} (i : Fin d) (κ : ℝ → ℝ)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (limitInput : TriadicDirichletLimitInput d i κ) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ∀ gap : ℝ, 0 < gap → gap ≤ ε →
      κ ((criticalPoint d:ℝ)+gap) ≤ D*gap^3*|Real.log gap| := by
  obtain ⟨ε0,D,hε0,hD,hbound⟩ := isotropic_finite_log_upper_of_standard_inputs i
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  let ε := min ε0 ((1-(criticalPoint d:ℝ))/2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,D,hε,hD,?_⟩
  intro gap hg hs
  have hs0 : gap ≤ ε0 := hs.trans (min_le_left _ _)
  have hstop : gap ≤ (1-(criticalPoint d:ℝ))/2 := hs.trans (min_le_right _ _)
  let p : unitInterval := ⟨(criticalPoint d:ℝ)+gap,by constructor <;> linarith⟩
  have hp : criticalPoint d < p := by change (criticalPoint d:ℝ) < (criticalPoint d:ℝ)+gap; linarith
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨S,_,hS⟩ := hbound gap hg hs0 η hη 0
  exact (triadic_limit_le_full_cube i limitInput p hp S).trans hS

end NearCritical
