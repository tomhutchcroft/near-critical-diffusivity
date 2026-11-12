module

public import NearCritical.CubeLowerBoundWater
public import NearCritical.TriadicDirichletLimit

/-! Water comparison for a SUPPLIED coefficient with the named standard
triadic limit property. Its existence and random-walk identification are separate. -/
@[expose] public section
noncomputable section
namespace NearCritical

theorem triadic_limit_le_relaxed_water {d : ℕ} (i : Fin d) {κ : ℝ → ℝ}
    (limitInput : TriadicDirichletLimitInput d i κ) (p : unitInterval)
    (hp : criticalPoint d < p) (r R : ℕ) :
    κ (p : ℝ) ≤ annealedRelaxed (waterCube d i r R) i (p : ℝ) +
      (2*(r : ℝ)+1)^2 * (d-1 : ℕ) / (2*R+1 : ℕ) :=
  cube_lower_bound_le_relaxed_water i p (κ (p : ℝ))
    (fun S => triadic_limit_le_full_cube i limitInput p hp S) r R

/-- An ACTUAL relaxed mean bound on cofinally wide boxes suffices. No bound
on the supplied limit coefficient is assumed, and no new coefficient is defined. -/
theorem triadic_limit_le_of_cofinal_relaxed_bound {d : ℕ} (i : Fin d) {κ : ℝ → ℝ}
    (limitInput : TriadicDirichletLimitInput d i κ) (p : unitInterval)
    (hp : criticalPoint d < p) (r : ℕ) (B : ℝ)
    (hbound : ∀ R0 : ℕ, ∃ R : ℕ, R0 ≤ R ∧
      annealedRelaxed (waterCube d i r R) i (p : ℝ) ≤ B) : κ (p : ℝ) ≤ B := by
  let C : ℝ := (2*(r : ℝ)+1)^2 * (d-1 : ℕ)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R0,hR0⟩ := exists_nat_gt (C/ε)
  obtain ⟨R,hR,hmean⟩ := hbound R0
  have hden : (R0 : ℝ) ≤ ((2*R+1 : ℕ) : ℝ) := by
    exact_mod_cast (show R0 ≤ 2*R+1 by omega)
  have hpos : (0 : ℝ) < (2*R+1 : ℕ) := by positivity
  have hmul : C < (R0 : ℝ)*ε := (div_lt_iff₀ hε).mp hR0
  have herr : C/(2*R+1 : ℕ) ≤ ε := by
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ (R0 : ℝ)*ε := hmul.le
      _ ≤ ((2*R+1 : ℕ) : ℝ)*ε := mul_le_mul_of_nonneg_right hden hε.le
      _ = ε*((2*R+1 : ℕ) : ℝ) := mul_comm _ _
  have h := triadic_limit_le_relaxed_water i limitInput p hp r R
  change κ (p : ℝ) ≤ annealedRelaxed (waterCube d i r R) i (p : ℝ)+C/(2*R+1 : ℕ) at h
  linarith

end NearCritical
