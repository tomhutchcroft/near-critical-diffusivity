module

public import NearCritical.MaskedWaterCubeNoLog
public import NearCritical.TriadicWaterComparison

@[expose] public section
noncomputable section
namespace NearCritical

/-- The finite no-log estimate passes to the supplied homogenized
conductivity through its actual triadic Dirichlet limit. The limit input
is a convergence and identification premise for the coefficient. -/
theorem homogenized_cubic_upper_of_standard_inputs {d : ℕ} (i : Fin d) (κ : ℝ → ℝ)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (limitInput : TriadicDirichletLimitInput d i κ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ gap : ℝ, 0 < gap → gap ≤ ε →
      κ ((criticalPoint d : ℝ)+gap) ≤ C*gap^3 := by
  obtain ⟨sharp, ε₀, C, _, _, hε₀, hC, hfinite⟩ :=
    waterCube_finite_cubic_upper_of_standard_inputs i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  let ε := min ε₀ ((1-(criticalPoint d : ℝ))/2)
  have hcap : 0 < (1-(criticalPoint d : ℝ))/2 := by linarith
  have hε : 0 < ε := lt_min hε₀ hcap
  refine ⟨ε, C, hε, hC, ?_⟩
  intro gap hg hsmall
  have hsmall₀ : gap ≤ ε₀ := hsmall.trans (min_le_left _ _)
  have hsmall₁ : gap ≤ (1-(criticalPoint d : ℝ))/2 := hsmall.trans (min_le_right _ _)
  let p : unitInterval := ⟨(criticalPoint d : ℝ)+gap, by constructor <;> linarith⟩
  have hp : criticalPoint d < p := by
    change (criticalPoint d : ℝ) < (criticalPoint d : ℝ)+gap
    linarith
  exact triadic_limit_le_of_cofinal_relaxed_bound i limitInput p hp
    (correlationRadius sharp gap) (C*gap^3)
    (fun R => ⟨R, le_rfl, hfinite R gap hg hsmall₀⟩)

/-- Full supercritical parameter range of the cubic conductivity upper
bound, conditional on the actual triadic Dirichlet-limit identification. -/
theorem homogenized_global_cubic_upper_of_standard_inputs {d : ℕ} (i : Fin d) (κ : ℝ → ℝ)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (limitInput : TriadicDirichletLimitInput d i κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : unitInterval, criticalPoint d < p →
      κ (p : ℝ) ≤ C*((p : ℝ)-(criticalPoint d : ℝ))^3 := by
  obtain ⟨ε, C₀, hε, hC₀, hlocal⟩ :=
    homogenized_cubic_upper_of_standard_inputs i κ hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1 limitInput
  let C := max C₀ (1/ε^3)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro p hp
  let gap := (p : ℝ)-(criticalPoint d : ℝ)
  have hg : 0 < gap := sub_pos.mpr hp
  change κ (p : ℝ) ≤ C*gap^3
  by_cases hsmall : gap ≤ ε
  · have h := hlocal gap hg hsmall
    have hp' : (criticalPoint d : ℝ)+gap = (p : ℝ) := by dsimp [gap]; ring
    rw [hp'] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hg.le _))
  · have hU : (centeredBox d 0).Nonempty := ⟨0, mem_centeredBox.mpr (fun _ => by simp)⟩
    have hκ : κ (p : ℝ) ≤ 1 :=
      ((triadic_limit_le_full_cube i limitInput p hp 0).trans
        (annealedFull_le_parameter _ hU i p)).trans p.property.2
    have hεg : ε^3 ≤ gap^3 := pow_le_pow_left₀ hε.le (le_of_not_ge hsmall) 3
    calc
      _ ≤ 1 := hκ
      _ = (1/ε^3)*ε^3 := by field_simp [hε.ne']
      _ ≤ (1/ε^3)*gap^3 := mul_le_mul_of_nonneg_left hεg (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hg.le _)

end NearCritical
