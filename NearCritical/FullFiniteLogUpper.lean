module
public import NearCritical.CenteredBoundaryComparison
public import NearCritical.HomogeneousFiniteLogUpper

/-! The finite error-removal step of lem.chain.2 and prop.upper_log. Full
Dirichlet boxes of arbitrarily large transverse width are constructed explicitly.
No infinite-volume conductivity is defined or identified by this theorem. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Actual finite patching removes both errors to any requested tolerance.
The displayed relaxed bound is a NEW modular input, instantiated below. -/
theorem full_waterCube_approx_of_uniform_relaxed_bound {d : ℕ} (i : Fin d)
    (r : ℕ) (p : unitInterval) {B : ℝ}
    (hrelaxed : ∀ R : ℕ, annealedRelaxed (waterCube d i r R) i (p:ℝ) ≤ B)
    {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∃ S : ℕ, K ≤ S ∧ annealedFull (waterCube d i r S) i (p:ℝ) ≤ B+η := by
  let A : ℝ := (2*(r:ℝ)+1)^2*(d-1:ℕ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨R,hR⟩ := exists_nat_gt (A/η)
  obtain ⟨m,hm⟩ := exists_nat_gt (max (K:ℝ) (2*(d-1:ℕ)/η))
  have hmK : K ≤ m := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hm))
  have hmA : 2*(d-1:ℕ)/η < (m:ℝ) := (le_max_right _ _).trans_lt hm
  have hRerr : A/(2*R+1:ℕ) ≤ η/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(2*R+1:ℕ))).mpr
    have ht := (div_lt_iff₀ hη).mp hR
    push_cast
    nlinarith
  have hmerr : 2*(d-1:ℕ)/(2*m+1:ℕ) ≤ η/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(2*m+1:ℕ))).mpr
    have ht := (div_lt_iff₀ hη).mp hmA
    push_cast
    nlinarith
  refine ⟨replicatedRadius R m,hmK.trans (replicatedRadius_ge R m),?_⟩
  have H := annealedFull_centered_boundary_comparison i r R m p
  have hbase := hrelaxed R
  change annealedFull (waterCube d i r (replicatedRadius R m)) i (p:ℝ) ≤
    annealedRelaxed (waterCube d i r R) i (p:ℝ)+
      2*(d-1:ℕ)/(2*m+1:ℕ)+A/(2*R+1:ℕ) at H
  linarith

/-- Actual FULL Dirichlet version of the finite cubic-log bound, with
arbitrarily small additive error on arbitrarily wide centered water cubes.
All NEW uniform-relaxed/patching/support assumptions are discharged. -/
theorem full_finite_log_upper_of_standard_inputs {d : ℕ} (i : Fin d)
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
        annealedFull (waterCube d i (correlationRadius 1 gap) S) i
          ((criticalPoint d:ℝ)+gap) ≤ D*gap^3*|Real.log gap|+η := by
  obtain ⟨ε0,D,hε0,hD,hbound⟩ := homogeneous_finite_log_upper_of_standard_inputs i
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  let ε := min ε0 ((1-(criticalPoint d:ℝ))/2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,D,hε,hD,?_⟩
  intro gap hg hs η hη K
  have hs0 : gap ≤ ε0 := hs.trans (min_le_left _ _)
  have hstop : gap ≤ (1-(criticalPoint d:ℝ))/2 := hs.trans (min_le_right _ _)
  let p : unitInterval := ⟨(criticalPoint d:ℝ)+gap,by
    constructor
    · linarith
    · linarith⟩
  exact full_waterCube_approx_of_uniform_relaxed_bound i (correlationRadius 1 gap) p
    (fun R => hbound R gap hg hs0) hη K

end NearCritical
