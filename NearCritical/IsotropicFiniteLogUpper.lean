module
public import NearCritical.DivisibleFullFiniteLogUpper
public import NearCritical.CubeWaterChain

/-! Actual cofinal isotropic full-Dirichlet upper-log bound. The separate
cube-to-water theorem is consumed unchanged. No limit or infinite-volume
conductivity identity is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- One cutoff/amplitude, actual centered ISOTROPIC cubes of arbitrarily large
radius, arbitrarily small additive error, and only named STANDARD inputs. -/
theorem isotropic_finite_log_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ∀ (gap : ℝ), 0 < gap → gap ≤ ε →
      ∀ (η : ℝ), 0 < η → ∀ K : ℕ, ∃ S : ℕ, K ≤ S ∧
        annealedFull (centeredBox d S) i ((criticalPoint d:ℝ)+gap) ≤
          D*gap^3*|Real.log gap|+η := by
  obtain ⟨ε0,D,hε0,hD,hbound⟩ := divisible_full_finite_log_upper_of_standard_inputs i
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  let ε := min ε0 ((1-(criticalPoint d:ℝ))/2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,D,hε,hD,?_⟩
  intro gap hg hs η hη K
  have hs0 : gap ≤ ε0 := hs.trans (min_le_left _ _)
  have hstop : gap ≤ (1-(criticalPoint d:ℝ))/2 := hs.trans (min_le_right _ _)
  let p : unitInterval := ⟨(criticalPoint d:ℝ)+gap,by constructor <;> linarith⟩
  obtain ⟨S,k,hKS,hside,hS⟩ := hbound gap hg hs0 η hη K
  refine ⟨S,hKS,?_⟩
  exact (annealedFull_cube_le_water_of_odd_multiple i (correlationRadius 1 gap) S k hside p).trans hS

end NearCritical
