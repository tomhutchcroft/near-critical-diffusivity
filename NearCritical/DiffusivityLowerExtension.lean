module

public import NearCritical.Section10ConductivityMonotone
public import NearCritical.TriadicLimitExistence
public import NearCritical.DiffusivityUpper

/-! Uniform extension of the coefficient lower bound.

* `fullCubeLimit_mono`: the constructed homogenized coefficient is monotone in
  the parameter (Rayleigh monotonicity and the monotone coupling, through
  `Section10.annealedFull_parameter_mono`).
* `fullCubeLimit_lowerPowerBound_of_near`: a cubic lower bound
  `c (p - p_c)^3 <= kappa(p)` on a window `(p_c, p_1]` extends to
  `LowerPowerBound p_c (fullCubeLimit d i) 3` on all of `(p_c, 1]`, with constant
  `c (p_1 - p_c)^3`.

So the energy half of `thm.main` only has to be proved near criticality; this
is the hypothesis of `einsteinDiffusivity_lower` / `einsteinDiffusivity_two_sided`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

variable {d : ℕ}

theorem fullCubeLimit_mono (i : Fin d) {p q : unitInterval} (hpq : p ≤ q) :
    fullCubeLimit d i (p : ℝ) ≤ fullCubeLimit d i (q : ℝ) := by
  unfold fullCubeLimit
  refine ciInf_mono ⟨0, ?_⟩ (fun L =>
    Section10.annealedFull_parameter_mono (zeroCube d (L + 1)) i hpq)
  rintro _ ⟨L, rfl⟩
  exact annealedFull_nonneg _ i p.2.1 p.2.2

theorem fullCubeLimit_lowerPowerBound_of_near (i : Fin d) {p1 c : ℝ}
    (hp1 : (criticalPoint d : ℝ) < p1) (hp1' : p1 ≤ 1) (hc : 0 < c)
    (hnear : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ p1 →
      c * (p - (criticalPoint d : ℝ)) ^ 3 ≤ fullCubeLimit d i p) :
    LowerPowerBound (criticalPoint d : ℝ) (fullCubeLimit d i) 3 := by
  have hpc0 : (0:ℝ) ≤ (criticalPoint d : ℝ) := (criticalPoint d).2.1
  have hg1 : 0 < p1 - (criticalPoint d : ℝ) := by linarith
  have hg1le : p1 - (criticalPoint d : ℝ) ≤ 1 := by linarith
  have hg1pow : (p1 - (criticalPoint d : ℝ)) ^ 3 ≤ 1 := pow_le_one₀ hg1.le hg1le
  refine ⟨c * (p1 - (criticalPoint d : ℝ)) ^ 3, by positivity, ?_⟩
  intro p hp hple
  have hg : 0 < p - (criticalPoint d : ℝ) := by linarith
  have hgle : p - (criticalPoint d : ℝ) ≤ 1 := by linarith
  have hgpow : (p - (criticalPoint d : ℝ)) ^ 3 ≤ 1 := pow_le_one₀ hg.le hgle
  by_cases h : p ≤ p1
  · have h1 := hnear p hp h
    have h2 : c * (p1 - (criticalPoint d : ℝ)) ^ 3 * (p - (criticalPoint d : ℝ)) ^ 3 ≤
        c * (p - (criticalPoint d : ℝ)) ^ 3 := by
      have hcg : 0 ≤ c * (p - (criticalPoint d : ℝ)) ^ 3 := by positivity
      calc c * (p1 - (criticalPoint d : ℝ)) ^ 3 * (p - (criticalPoint d : ℝ)) ^ 3
          = (c * (p - (criticalPoint d : ℝ)) ^ 3) * (p1 - (criticalPoint d : ℝ)) ^ 3 := by ring
        _ ≤ (c * (p - (criticalPoint d : ℝ)) ^ 3) * 1 := mul_le_mul_of_nonneg_left hg1pow hcg
        _ = _ := by ring
    exact h2.trans h1
  · have hlt : p1 < p := not_le.mp h
    have h1 := hnear p1 hp1 le_rfl
    have hmono := fullCubeLimit_mono i
      (p := ⟨p1, by linarith, hp1'⟩) (q := ⟨p, by linarith, hple⟩) hlt.le
    have h2 : c * (p1 - (criticalPoint d : ℝ)) ^ 3 * (p - (criticalPoint d : ℝ)) ^ 3 ≤
        c * (p1 - (criticalPoint d : ℝ)) ^ 3 := by
      have hcg : 0 ≤ c * (p1 - (criticalPoint d : ℝ)) ^ 3 := by positivity
      calc c * (p1 - (criticalPoint d : ℝ)) ^ 3 * (p - (criticalPoint d : ℝ)) ^ 3
          ≤ c * (p1 - (criticalPoint d : ℝ)) ^ 3 * 1 := mul_le_mul_of_nonneg_left hgpow hcg
        _ = _ := by ring
    exact h2.trans (h1.trans hmono)

end NearCritical
