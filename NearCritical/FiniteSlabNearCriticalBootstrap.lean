module

public import NearCritical.CriticalSlabBoundaryFamily

/-! NEW finite-slab near-critical bootstrap. The maximum is never differentiated;
all differential inequalities refer to actual polynomial row/column coordinates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Instantiate the proved finite-family first-crossing argument with actual
finite-slab row/column polynomials and the proved Russo cubic inequality. -/
theorem finiteSlabBoundaryMaximum_nearCritical_of_small {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (N : ℕ) (p : unitInterval)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c)
    (hp : (criticalPoint d : ℝ) ≤ (p : ℝ))
    (hsmall : 16 * (2 * (d : ℝ) * (N+1 : ℝ)^2) *
      (4*C/(criticalPoint d : ℝ)^2)^2 * ((p : ℝ)-(criticalPoint d : ℝ)) ≤ 1) :
    finiteSlabBoundaryMaximum (p : ℝ) U i 0 (N : ℤ) ≤
      2 * (4*C/(criticalPoint d : ℝ)^2) := by
  let K : ℝ := 4*C/(criticalPoint d : ℝ)^2
  let L : ℝ := 2*(d : ℝ)*(N+1 : ℝ)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb := finite_family_cubic_bootstrap_of_contDiffOn
    (finiteSlabBoundaryFamily U i 0 (N : ℤ)) hK hL
    (fun a ↦ (finiteSlabBoundaryFamily_contDiff 1 U i 0 (N : ℤ) a).contDiffOn)
    (fun a q hq ↦ finiteSlabBoundaryFamily_nonneg q (hpc.le.trans hq.1)
      (hq.2.trans p.2.2) U i 0 (N : ℤ) a)
    (fun a ↦ finiteSlabBoundaryFamily_critical_le U i 0 (N : ℤ) a hC hc hpc decay)
    (fun a q hq ↦ ?_) hsmall
  · exact finiteFamilyMaximum_le _ _ _ (fun a ↦ hb (p : ℝ) ⟨hp, le_rfl⟩ a)
  · let q' : unitInterval := ⟨q, ⟨hpc.le.trans hq.1.le, hq.2.le.trans p.2.2⟩⟩
    have hq1 : (q' : ℝ) ≠ 1 := ne_of_lt (hq.2.trans_le p.2.2)
    exact finiteSlabBoundaryFamily_deriv_le_cubic_nat q' hq1 U i N a

/-- A single positive window and bound are chosen BEFORE cutoff U, slab height
N and parameter p. Only the explicit cited weighted critical pioneer estimate
is assumed; the finite initial bound and differential inequality are proved. -/
theorem finiteSlabBoundaryMaximum_nearCritical_uniform {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (U : Finset (Vertex d)) (N : ℕ) (p : unitInterval),
        (criticalPoint d : ℝ) ≤ (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        finiteSlabBoundaryMaximum (p : ℝ) U i 0 (N : ℤ) ≤ 2*K := by
  let K : ℝ := 4*C/(criticalPoint d : ℝ)^2
  have hK : 0 < K := by dsimp [K]; positivity
  let D : ℝ := 32*((d : ℝ)+1)*K^2
  have hD : 0 < D := by dsimp [D]; positivity
  let ε : ℝ := min ((1-(criticalPoint d : ℝ))/2) (1/D)
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεhalf : ε ≤ (1-(criticalPoint d : ℝ))/2 := min_le_left _ _
  have hεD : D*ε ≤ 1 := by
    have h := (le_div_iff₀ hD).mp (show ε ≤ 1/D from min_le_right _ _)
    simpa only [mul_comm] using h
  refine ⟨ε, K, hε, hK, by linarith, ?_⟩
  intro U N p hp hpwin
  apply finiteSlabBoundaryMaximum_nearCritical_of_small U i N p hC hc hpc decay hp
  have hA : 0 < (N+1 : ℝ)^2 := by positivity
  have hgap : ((p : ℝ)-(criticalPoint d : ℝ))*(N+1 : ℝ)^2 ≤ ε :=
    (le_div_iff₀ hA).mp (by linarith : (p : ℝ)-(criticalPoint d : ℝ) ≤ ε/(N+1 : ℝ)^2)
  change 16*(2*(d : ℝ)*(N+1 : ℝ)^2)*K^2*((p : ℝ)-(criticalPoint d : ℝ)) ≤ 1
  calc
    _ = (32*(d : ℝ)*K^2)*(((p : ℝ)-(criticalPoint d : ℝ))*(N+1 : ℝ)^2) := by ring
    _ ≤ (32*(d : ℝ)*K^2)*ε := mul_le_mul_of_nonneg_left hgap (by positivity)
    _ ≤ D*ε := by dsimp [D]; nlinarith [sq_nonneg K]
    _ ≤ 1 := hεD

end NearCritical
