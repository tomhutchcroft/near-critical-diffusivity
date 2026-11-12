import NearCritical.ExternalLawBridge
import NearCritical.PercolationMonotonicity

/-!
The mean-field lower bound for the project's own percolation density,

  `p - p_c <= density d p`   for every `p > p_c`,

with `density d p = P_p[0 <-> infinity]` and `criticalPoint d` the project's
objects. This is the cited density input (`barsky1991` / Aizenman--Barsky,
here through the imported Duminil-Copin--Tassion argument) of the diffusivity
reductions, now a theorem with no hypotheses.

Route: by the model-law bridge the imported `theta (zdGraph d) 0` is the
project's `density d`. If `density d q > 0` with `q < 1` then `phi_q(S) >= 1`
for every finite `S` containing the origin (otherwise the imported exponential
decay forces `density d q = 0`). Monotonicity of `phi` and the imported
mean-field step give `(p - p1)/(p (1 - p1)) <= density d p` for
`p_c < p1 < p < 1`; letting `p1` decrease to `p_c` gives the claim, and `p = 1`
follows by monotonicity of the density.

-/

namespace NearCritical.External
open MeasureTheory
open Percolation.Literature Percolation.Literature.LatticeModels Percolation.Literature.DCT16

/-- Exponential decay to zero, elementary form. -/
lemma exists_exp_neg_mul_lt {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ n : ℕ, Real.exp (-c * n) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (c * ε))
  refine ⟨n, ?_⟩
  have hcε : 0 < c * ε := mul_pos hc hε
  have hn' : 1 < c * ε * n := by
    have h := (div_lt_iff₀ hcε).mp hn
    linarith
  have hnpos : (0:ℝ) < n := by
    by_contra hneg
    have : c * ε * (n:ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcε.le (not_lt.mp hneg)
    linarith
  have hexp : c * n + 1 ≤ Real.exp (c * n) := Real.add_one_le_exp _
  have hlt : ε⁻¹ < Real.exp (c * n) := by
    have h1 : ε⁻¹ < c * n := by
      rw [inv_lt_iff_one_lt_mul₀' hε]
      linarith
    linarith
  have hrw : Real.exp (-c * n) = (Real.exp (c * n))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hrw]
  exact (inv_lt_comm₀ (Real.exp_pos _) hε).mpr hlt

/-- Positive density at a parameter `q < 1` forces `phi_q(S) >= 1` for every
finite set containing the origin. -/
theorem phi_ge_one_of_density_pos {d : ℕ} (q : unitInterval) (hq1 : (q:ℝ) < 1)
    (hpos : 0 < NearCritical.density d q) (S : Finset (Site d)) (h0 : (0 : Site d) ∈ S) :
    1 ≤ DCT16.phi q S := by
  by_contra hlt
  obtain ⟨c, hc, hdecay⟩ :=
    DCT16_expDecay_of_phi_lt_one_holds q S h0 (not_le.mp hlt) hq1
  obtain ⟨n, hn⟩ := exists_exp_neg_mul_lt hc hpos
  have hθ : NearCritical.density d q ≤ Real.exp (-c * n) := by
    rw [← theta_eq_density]
    exact (theta_le_real_siteToBoundary q n).trans (hdecay n)
  linarith

/-- The imported mean-field step for the project's density. -/
theorem density_ge_meanField {d : ℕ} (p₁ p : unitInterval)
    (h₁ : NearCritical.criticalPoint d < p₁) (h : (p₁:ℝ) < p) (hp1 : (p:ℝ) < 1) :
    ((p:ℝ) - p₁) / (p * (1 - p₁)) ≤ NearCritical.density d p := by
  rw [← theta_eq_density]
  refine DCT16_meanField_of_phi_ge_one_holds p₁ ?_ p h hp1
  intro q hq S h0
  exact (phi_ge_one_of_density_pos p₁ (h.trans hp1)
    (NearCritical.density_pos_above_critical h₁) S h0).trans (DCT16_phi_mono_holds S hq)

/-- Mean-field bound below `1`. -/
theorem density_ge_gap_of_lt_one {d : ℕ} (p : unitInterval)
    (hp : NearCritical.criticalPoint d < p) (hp1 : (p:ℝ) < 1) :
    (p:ℝ) - (NearCritical.criticalPoint d : ℝ) ≤ NearCritical.density d p := by
  by_contra hlt
  have hlt' := not_le.mp hlt
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = NearCritical.density d p := ⟨_, rfl⟩
  rw [← hδ] at hlt'
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact measureReal_nonneg
  have hpc0 : (0:ℝ) ≤ (NearCritical.criticalPoint d : ℝ) := (NearCritical.criticalPoint d).2.1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((NearCritical.criticalPoint d : ℝ) + ((p:ℝ) - δ)) / 2 :=
    ⟨_, rfl⟩
  have hm1 : (NearCritical.criticalPoint d : ℝ) < m := by
    rw [hm]
    linarith
  have hm2 : m < (p:ℝ) - δ := by
    rw [hm]
    linarith
  have hmI : m ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcrit : NearCritical.criticalPoint d < (⟨m, hmI⟩ : unitInterval) := hm1
  have hmp : ((⟨m, hmI⟩ : unitInterval) : ℝ) < p := by
    change m < (p:ℝ)
    linarith
  have hmf := density_ge_meanField (⟨m, hmI⟩ : unitInterval) p hcrit hmp hp1
  change ((p:ℝ) - m) / ((p:ℝ) * (1 - m)) ≤ NearCritical.density d p at hmf
  rw [← hδ] at hmf
  have hpm : 0 < (p:ℝ) - m := by linarith
  have hp0 : 0 < (p:ℝ) := by linarith
  have h1m : 0 < 1 - m := by linarith
  have hden : 0 < (p:ℝ) * (1 - m) := mul_pos hp0 h1m
  have hden1 : (p:ℝ) * (1 - m) ≤ 1 := by
    have h1 : (p:ℝ) * (1 - m) ≤ 1 * 1 :=
      mul_le_mul p.2.2 (by linarith) h1m.le zero_le_one
    linarith
  have hge : (p:ℝ) - m ≤ ((p:ℝ) - m) / ((p:ℝ) * (1 - m)) := by
    rw [le_div_iff₀ hden]
    exact mul_le_of_le_one_right hpm.le hden1
  linarith

/-- **Mean-field lower bound for the project's density**: `p - p_c <= theta(p)`
for every `p > p_c`. Unconditional. -/
theorem density_ge_gap {d : ℕ} (p : unitInterval) (hp : NearCritical.criticalPoint d < p) :
    (p:ℝ) - (NearCritical.criticalPoint d : ℝ) ≤ NearCritical.density d p := by
  by_cases hp1 : (p:ℝ) < 1
  · exact density_ge_gap_of_lt_one p hp hp1
  · have hpe : (p:ℝ) = 1 := le_antisymm p.2.2 (not_lt.mp hp1)
    by_contra hlt
    have hlt' := not_le.mp hlt
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = NearCritical.density d p := ⟨_, rfl⟩
    rw [← hδ, hpe] at hlt'
    have hδ0 : 0 ≤ δ := by
      rw [hδ]
      exact measureReal_nonneg
    have hpc0 : (0:ℝ) ≤ (NearCritical.criticalPoint d : ℝ) :=
      (NearCritical.criticalPoint d).2.1
    obtain ⟨q, hq⟩ : ∃ q : ℝ,
        q = 1 - (1 - (NearCritical.criticalPoint d : ℝ) - δ) / 2 := ⟨_, rfl⟩
    have hq1 : q < 1 := by
      rw [hq]
      linarith
    have hqc : (NearCritical.criticalPoint d : ℝ) < q := by
      rw [hq]
      linarith
    have hqI : q ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hq1.le⟩
    have hcrit : NearCritical.criticalPoint d < (⟨q, hqI⟩ : unitInterval) := hqc
    have hgap := density_ge_gap_of_lt_one (⟨q, hqI⟩ : unitInterval) hcrit hq1
    change q - (NearCritical.criticalPoint d : ℝ) ≤ _ at hgap
    have hqp : (⟨q, hqI⟩ : unitInterval) ≤ p := by
      change q ≤ (p:ℝ)
      linarith
    have hmono := NearCritical.density_monotone d hqp
    rw [← hδ] at hmono
    have hqgap : δ < q - (NearCritical.criticalPoint d : ℝ) := by
      rw [hq]
      linarith
    linarith

/-- The density lower bound in the exact shape consumed by the diffusivity
reductions (`hθlo` with constant `1`), for the project's density read on real
parameters. -/
theorem density_lower_real (d : ℕ) :
    ∀ p : ℝ, (NearCritical.criticalPoint d : ℝ) < p → p ≤ 1 →
      1 * (p - (NearCritical.criticalPoint d : ℝ)) ≤
        NearCritical.density d (Set.projIcc 0 1 zero_le_one p) := by
  intro p hp hp1
  have hp0 : (0:ℝ) ≤ p := le_trans (NearCritical.criticalPoint d).2.1 hp.le
  have hproj : Set.projIcc (0:ℝ) 1 zero_le_one p = ⟨p, hp0, hp1⟩ :=
    Set.projIcc_of_mem zero_le_one ⟨hp0, hp1⟩
  rw [hproj, one_mul]
  have hcrit : NearCritical.criticalPoint d < (⟨p, hp0, hp1⟩ : unitInterval) := hp
  exact density_ge_gap (⟨p, hp0, hp1⟩ : unitInterval) hcrit

end NearCritical.External
