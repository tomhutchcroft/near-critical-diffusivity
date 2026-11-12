module

public import NearCritical.SlabPioneerExhaustion
public import NearCritical.SlabSusceptibility
public import NearCritical.PercolationMonotonicity

/-! NEW slab threshold lower bound. The final probability input is the actual
susceptibility deduction, not an assumed absence of an infinite cluster. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Zero actual restricted density cannot occur strictly above the actual
restricted critical point, by proved endpoint-inclusive parameter monotonicity. -/
lemma parameter_le_restrictedCriticalPoint_of_density_zero {d : ℕ}
    (S : Set (Vertex d)) (p : unitInterval) (hz : restrictedDensity d S p = 0) :
    p ≤ restrictedCriticalPoint d S := by
  by_contra h
  have hp := restrictedDensity_pos_above_critical (lt_of_not_ge h)
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- The source codimension-one slab is literally the finite height slab in
the last coordinate, with no change of probability law or graph model. -/
lemma finiteHeightSlab_last_eq_slabVertices {d : ℕ} (hd : 0 < d) (N : ℕ) :
    finiteHeightSlab (⟨d-1, by omega⟩ : Fin d) 0 (N : ℤ) = slabVertices d (d-1) N := by
  ext x
  change (0 ≤ x (⟨d-1, by omega⟩ : Fin d) ∧ x (⟨d-1, by omega⟩ : Fin d) ≤ (N : ℤ)) ↔
    ∀ j : Fin d, d-1 ≤ j.val → 0 ≤ x j ∧ x j ≤ (N : ℤ)
  constructor
  · intro hx j hj
    have he : j = (⟨d-1, by omega⟩ : Fin d) := Fin.ext (by change j.val = d-1; omega)
    simpa only [he] using hx
  · intro hx
    exact hx (⟨d-1, by omega⟩ : Fin d) le_rfl

/-- Exact source-window normalization for N>=1; no asymptotic inequality is
used at the small-height endpoint N=1. -/
lemma slab_window_inverse_sq_lower {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) (hN : 1 ≤ N) :
    (ε/4)/(N : ℝ)^2 ≤ ε/(N+1 : ℝ)^2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (div_le_div_iff₀ (by positivity : 0 < (N : ℝ)^2)
    (by positivity : 0 < (N+1 : ℝ)^2)).mpr
  nlinarith [mul_nonneg hε (show 0 ≤ 4*(N : ℝ)^2-(N+1 : ℝ)^2 by nlinarith)]

private lemma slab_window_parameter_exists {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hpc : 0 < (criticalPoint d : ℝ)) (hend : (criticalPoint d : ℝ)+ε < 1)
    (N : ℕ) : ∃ p : unitInterval,
      (p : ℝ) = (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hA : 1 ≤ (N+1 : ℝ)^2 := by nlinarith
  have hAp : 0 < (N+1 : ℝ)^2 := by positivity
  have hfrac : ε/(N+1 : ℝ)^2 ≤ ε := (div_le_iff₀ hAp).mpr (by nlinarith)
  refine ⟨⟨(criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2, ?_, ?_⟩, rfl⟩
  · positivity
  · linarith

/-- Pure threshold/window algebra. The final STANDARD-input theorem below
will supply this zero-density window from actual slab susceptibility. -/
private lemma slab_critical_gap_of_zero_density_window {d : ℕ} (i : Fin d)
    {ε : ℝ} (hε : 0 < ε) (hpc : 0 < (criticalPoint d : ℝ))
    (hend : (criticalPoint d : ℝ)+ε < 1)
    (hzero : ∀ (N : ℕ) (p : unitInterval), (criticalPoint d : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
      restrictedDensity d (finiteHeightSlab i 0 (N : ℤ)) p = 0) :
    ∀ N : ℕ, 1 ≤ N → (ε/4)/(N : ℝ)^2 ≤
      (restrictedCriticalPoint d (finiteHeightSlab i 0 (N : ℤ)) : ℝ) -
        (criticalPoint d : ℝ) := by
  intro N hN
  obtain ⟨p, hp⟩ := slab_window_parameter_exists hε hpc hend N
  have hplo : (criticalPoint d : ℝ) ≤ (p : ℝ) := by
    rw [hp]
    exact le_add_of_nonneg_right (by positivity)
  have hz := hzero N p hplo (by rw [hp])
  have hcrit : (p : ℝ) ≤ (restrictedCriticalPoint d (finiteHeightSlab i 0 (N : ℤ)) : ℝ) :=
    parameter_le_restrictedCriticalPoint_of_density_zero _ p hz
  rw [hp] at hcrit
  have hnorm := slab_window_inverse_sq_lower hε.le N hN
  linarith

/-- NEW literal slab threshold lower bound in any selected coordinate.
The zero-density premise of the private algebra is supplied INTERNALLY by the
proved actual slab susceptibility theorem and actual near-critical mass bound.
Only the cited weighted critical pioneer input and pc interior remain. -/
theorem finiteHeightSlab_critical_lower_of_weighted {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, 1 ≤ N → a/(N : ℝ)^2 ≤
      (restrictedCriticalPoint d (finiteHeightSlab i 0 (N : ℤ)) : ℝ) -
        (criticalPoint d : ℝ) := by
  obtain ⟨ε, K, hε, hK, hend, hmass⟩ :=
    slabPioneerMass_nearCritical_upper_of_weighted i hC hc hpc hpc1 decay
  refine ⟨ε/4, by positivity, slab_critical_gap_of_zero_density_window i hε hpc hend ?_⟩
  intro N p hp hpwin
  obtain ⟨_, hwhole⟩ := hmass N p hp hpwin
  apply slab_restrictedDensity_zero_of_plane_bound p i N ((N+1 : ℝ)*(2*K)^2) (by positivity)
  intro j hj
  exact hwhole 0 (Finset.mem_Icc.mpr ⟨le_rfl, by positivity⟩) j hj

/-- The LOWER branch of literal source Theorem 1.3 (thm.slab), for its actual
codimension-one slab. This conditional statement does not claim the upper
branch or instantiate its explicit STANDARD weighted critical pioneer input. -/
theorem slabCriticalPoint_lower_of_weighted {d : ℕ} (hd : 0 < d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d)
      (⟨d-1, by omega⟩ : Fin d) C c) :
    ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, 1 ≤ N → a/(N : ℝ)^2 ≤
      (restrictedCriticalPoint d (slabVertices d (d-1) N) : ℝ) - (criticalPoint d : ℝ) := by
  obtain ⟨a, ha, hbound⟩ := finiteHeightSlab_critical_lower_of_weighted
    (⟨d-1, by omega⟩ : Fin d) hC hc hpc hpc1 decay
  refine ⟨a, ha, ?_⟩
  intro N hN
  rw [← finiteHeightSlab_last_eq_slabVertices hd N]
  exact hbound N hN

end NearCritical
