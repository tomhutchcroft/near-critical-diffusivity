import NearCritical.DiffusivityActualDensity

/-!
The LOWER half of `thm.main` for the Einstein-relation diffusivity, reduced to
the coefficient lower bound, and the two-sided statement.

Convention: the formal target of `thm.main` is
`einsteinDiffusivity d i p = 2 kappa(p) / theta(p)`.

* `uniform_einstein_lower`: a cubic lower bound on the conductivity and a linear
  UPPER bound on a positive density give a quadratic lower bound on any
  `variance` satisfying the Einstein identity.
* `einsteinDiffusivity_lower`: for `kappa = fullCubeLimit d i` and the actual
  density, `c (p - p_c)^2 <= einsteinDiffusivity d i p` on `(p_c, 1]`, from
  - `LowerPowerBound p_c (fullCubeLimit d i) 3` (the energy lower bound of the
    paper: NOT proved here; it is the open half of `thm.main`), and
  - `UpperPowerBound p_c (densityReal d) 1` (the cited mean-field upper bound
    `theta(p) <= C (p - p_c)`; source main.tex 536-538).
  Positivity of the density is the proved `External.density_lower_real`.
* `einsteinDiffusivity_two_sided`: with the proved upper bound
  `einsteinDiffusivity_upper`, constants `0 < c <= C` with
  `c (p - p_c)^2 <= einsteinDiffusivity d i p <= C (p - p_c)^2` on `(p_c, 1]`.
-/

namespace NearCritical
noncomputable section

theorem uniform_einstein_lower {pc : ℝ} {conductivity density variance : ℝ → ℝ}
    (hA : LowerPowerBound pc conductivity 3)
    (hθ : UpperPowerBound pc density 1)
    (hpos : ∀ p : ℝ, pc < p → p ≤ 1 → 0 < density p)
    (hE : ∀ p : ℝ, pc < p → p ≤ 1 → variance p / 2 = conductivity p / density p) :
    LowerPowerBound pc variance 2 := by
  obtain ⟨c, hc, hκ⟩ := hA
  obtain ⟨C, hC, hden⟩ := hθ
  refine ⟨2 * c / C, by positivity, ?_⟩
  intro p hp hp1
  have hg : 0 < p - pc := by linarith
  have h1 := hκ p hp hp1
  have h2 := hden p hp hp1
  have h3 := hpos p hp hp1
  have hvar : variance p = 2 * (conductivity p / density p) := by
    have := hE p hp hp1
    linarith
  rw [hvar]
  have hCg : 0 < C * (p - pc) := mul_pos hC hg
  have hstep : c * (p - pc) ^ 3 / (C * (p - pc)) ≤ conductivity p / density p := by
    rw [div_le_div_iff₀ hCg h3]
    have hk0 : 0 ≤ c * (p - pc) ^ 3 := by positivity
    have h2' : density p ≤ C * (p - pc) := by simpa using h2
    calc c * (p - pc) ^ 3 * density p ≤ c * (p - pc) ^ 3 * (C * (p - pc)) :=
          mul_le_mul_of_nonneg_left h2' hk0
      _ ≤ conductivity p * (C * (p - pc)) := mul_le_mul_of_nonneg_right h1 hCg.le
  have heq : 2 * c / C * (p - pc) ^ 2 = 2 * (c * (p - pc) ^ 3 / (C * (p - pc))) := by
    field_simp
  rw [heq]
  linarith

/-- **Lower bound of `thm.main` for the Einstein-relation diffusivity**, from the
coefficient lower bound and the cited density upper bound. -/
theorem einsteinDiffusivity_lower {d : ℕ} (i : Fin d)
    (hκ : LowerPowerBound (criticalPoint d : ℝ) (fullCubeLimit d i) 3)
    (hθ : UpperPowerBound (criticalPoint d : ℝ) (densityReal d) 1) :
    LowerPowerBound (criticalPoint d : ℝ) (einsteinDiffusivity d i) 2 := by
  refine uniform_einstein_lower hκ hθ ?_ ?_
  · intro p hp hp1
    have h := External.density_lower_real d p hp hp1
    have hg : 0 < p - (criticalPoint d : ℝ) := by linarith
    change 0 < density d (Set.projIcc 0 1 zero_le_one p)
    linarith
  · intro p _ _
    unfold einsteinDiffusivity
    ring

/-- **`thm.main` for the Einstein-relation diffusivity, two-sided**, modulo the
coefficient lower bound. -/
theorem einsteinDiffusivity_two_sided {d : ℕ} (i : Fin d) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hκ : LowerPowerBound (criticalPoint d : ℝ) (fullCubeLimit d i) 3)
    (hθ : UpperPowerBound (criticalPoint d : ℝ) (densityReal d) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      c * (p - (criticalPoint d : ℝ)) ^ 2 ≤ einsteinDiffusivity d i p ∧
        einsteinDiffusivity d i p ≤ C * (p - (criticalPoint d : ℝ)) ^ 2 := by
  obtain ⟨c, hc, hlo⟩ := einsteinDiffusivity_lower i hκ hθ
  obtain ⟨C, hC, hup⟩ := einsteinDiffusivity_upper i hB hb hCo hpc1 pioneers ordinary δ hδ hδ1
  exact ⟨c, C, hc, hC, fun p hp hp1 => ⟨hlo p hp hp1, hup p hp hp1⟩⟩

end
end NearCritical
