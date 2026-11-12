module

public import NearCritical.RegularityEnergyTails

/-! Numerical parameter order in NEW prop.choice_c: fix the heart fraction
before all error tolerances, then choose a large radius. No moment diagram
estimate or eventual-in-n hypothesis is supplied by these numerical lemmas. -/
@[expose] public section
noncomputable section
namespace NearCritical

private lemma regularity_radius_le_pow (r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q) :
    (r:ℝ) ≤ (r:ℝ)^q := by
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hp : (1:ℝ) ≤ (r:ℝ)^(q-1) := one_le_pow₀ hrR
  calc
    (r:ℝ) = 1*(r:ℝ) := by ring
    _ ≤ (r:ℝ)^(q-1)*(r:ℝ) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (r:ℝ)^q := by
      rw [← pow_succ]
      congr 1
      omega

/-- ONE positive heart fraction and a radius threshold make the source mean
profile at most delta/2. The fraction does not depend on a later error budget. -/
theorem exists_regularity_mean_scales {d : ℕ} (hd : 7 ≤ d)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/16 ∧ ∃ r0 : ℕ, 1 ≤ r0 ∧
      ∀ r : ℕ, r0 ≤ r → C*(ρ^(d-4)+1/(r:ℝ)^(d-6)) ≤ δ/2 := by
  let ρ : ℝ := min (1/16) (δ/(4*(C+1)))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ16 : ρ ≤ 1/16 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := by linarith
  have hρsmall : ρ ≤ δ/(4*(C+1)) := min_le_right _ _
  have hρprod : ρ*(4*(C+1)) ≤ δ :=
    (le_div_iff₀ (by positivity : (0:ℝ) < 4*(C+1))).mp hρsmall
  have hρpow : ρ^(d-4) ≤ ρ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (show 1 ≤ d-4 by omega)
  have hmeanρ : C*ρ^(d-4) ≤ δ/4 := by
    have hm := mul_le_mul_of_nonneg_left hρpow hC
    nlinarith
  obtain ⟨r0,hr0⟩ := exists_nat_ge (max (1:ℝ) (4*(C+1)/δ))
  have hr01 : 1 ≤ r0 := by exact_mod_cast (le_max_left (1:ℝ) (4*(C+1)/δ)).trans hr0
  have hscale : 4*(C+1)/δ ≤ (r0:ℝ) := (le_max_right _ _).trans hr0
  refine ⟨ρ,hρ,hρ16,r0,hr01,?_⟩
  intro r hr
  have hrr : (r0:ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : 1 ≤ r := hr01.trans hr
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hδr : 4*(C+1) ≤ (r:ℝ)*δ := (div_le_iff₀ hδ).mp (hscale.trans hrr)
  have hpow := regularity_radius_le_pow r (d-6) hr1 (by omega)
  have hmeanr : C/(r:ℝ)^(d-6) ≤ δ/4 := by
    apply (div_le_iff₀ (pow_pos hrR _)).mpr
    have hm := mul_le_mul_of_nonneg_left hpow hδ.le
    nlinarith
  have he : C*(ρ^(d-4)+1/(r:ℝ)^(d-6)) = C*ρ^(d-4)+C/(r:ℝ)^(d-6) := by ring
  rw [he]
  linarith

/-- Reciprocal radius powers eventually meet any positive budget, with an
arbitrary prior radius threshold retained. This is the r-selection step only. -/
theorem exists_regularity_decay_radius {d : ℕ} (hd : 7 ≤ d) (K : ℝ) (r0 : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, r0 ≤ R ∧ 1 ≤ R ∧ ∀ r : ℕ, R ≤ r → K/(r:ℝ)^(d-6) ≤ ε := by
  obtain ⟨R,hR⟩ := exists_nat_ge (max (r0:ℝ) (max 1 (K/ε)))
  have hr0 : r0 ≤ R := by exact_mod_cast (le_max_left (r0:ℝ) (max 1 (K/ε))).trans hR
  have hR1 : 1 ≤ R := by
    exact_mod_cast (le_trans (le_max_left (1:ℝ) (K/ε)) (le_trans (le_max_right _ _) hR))
  have hscale : K/ε ≤ (R:ℝ) :=
    (le_max_right (1:ℝ) (K/ε)).trans ((le_max_right _ _).trans hR)
  refine ⟨R,hr0,hR1,?_⟩
  intro r hr
  have hrr : (R:ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : 1 ≤ r := hR1.trans hr
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hK : K ≤ (r:ℝ)*ε := (div_le_iff₀ hε).mp (hscale.trans hrr)
  have hpow := regularity_radius_le_pow r (d-6) hr1 (by omega)
  apply (div_le_iff₀ (pow_pos hrR _)).mpr
  have hm := mul_le_mul_of_nonneg_left hpow hε.le
  nlinarith

/-- Source quantifier order: fixed rho first, THEN every epsilon gets a radius
threshold. K may depend on rho, as the source variance constants do.
Actual diagram/geometry inputs and eventual n-cutoffs remain separate. -/
theorem exists_regularity_parameter_choices {d : ℕ} (hd : 7 ≤ d)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (K : ℝ → ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/16 ∧ ∀ ε : ℝ, 0 < ε →
      ∃ R : ℕ, 1 ≤ R ∧ ∀ r : ℕ, R ≤ r →
        C*(ρ^(d-4)+1/(r:ℝ)^(d-6)) ≤ δ/2 ∧ K ρ/(r:ℝ)^(d-6) ≤ ε := by
  obtain ⟨ρ,hρ,hρ16,r0,hr0,hmean⟩ := exists_regularity_mean_scales hd hC hδ
  refine ⟨ρ,hρ,hρ16,?_⟩
  intro ε hε
  obtain ⟨R,hr0R,hR,hdecay⟩ := exists_regularity_decay_radius hd (K ρ) r0 hε
  exact ⟨R,hR,fun r hr => ⟨hmean r (hr0R.trans hr),hdecay r hr⟩⟩

end NearCritical
