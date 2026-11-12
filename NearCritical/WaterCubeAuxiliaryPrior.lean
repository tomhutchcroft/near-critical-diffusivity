module
public import NearCritical.WaterCubeSubcriticalPrior

/-! NEW homogeneous lem.bb_bound from the actual proved product envelope.
Both orientations, closed tested bonds, and the full issued sum are retained.
Also supplies literal log h conversion for odd heights at least three. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory

/-- Auxiliary-energy completion of the issued-edge summation in eq.aa_bound_step2.
The harmless `1 + log h` retains the degenerate h=1 cube explicitly. -/
theorem annealedB_waterCube_le_of_productEnvelope {d : ℕ} (i : Fin d)
    (r R : ℕ) {l h : DomainVertex (waterCube d i r R)}
    (hl : l ∈ negativeFace (waterCube d i r R) i)
    (hh : h ∈ positiveFace (waterCube d i r R) i)
    (p : unitInterval) {C : ℝ} (hC : 0 ≤ C)
    (henv : WaterCubeConnectionProductEnvelope i r R p C) :
    annealedB (waterCube d i r R) i (p : ℝ) ≤
      2 * (d : ℝ) * C * (1 + Real.log (2 * r + 1 : ℕ)) /
        (2 * (r : ℝ) + 1) ^ 2 := by
  have hs := sum_issued_waterCube_inverse_depth_le i r R
  have hsum : (∑ e : IssuedBond (waterCube d i r R),
      boundaryConnectionProducts (waterCube d i r R) i p e) ≤
      (C / (2 * (r : ℝ) + 1) ^ 3) *
        (2 * (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) *
          (1 + Real.log (2 * r + 1 : ℕ))) := by
    calc
      _ ≤ ∑ e : IssuedBond (waterCube d i r R),
          (C / (2 * (r : ℝ) + 1) ^ 3) *
            (1 / (waterCubeBaseDepth i r e.val.1 + 1 : ℝ)) :=
        sum_le_sum fun e _ => henv e
      _ = _ := by rw [← mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (div_nonneg hC (by positivity))
  have hr : (0 : ℝ) < 2 * (r : ℝ) + 1 := by positivity
  have hM : (0 : ℝ) < ((2 * R + 1) ^ (d - 1) : ℕ) := by positivity
  calc
    _ ≤ ((coordinateData i h - coordinateData i l) ^ 2 /
        ((waterCube d i r R).card : ℝ)) *
        ∑ e : IssuedBond (waterCube d i r R),
          boundaryConnectionProducts (waterCube d i r R) i p e :=
      annealedB_le_connectionProducts _ i hl hh p
    _ ≤ ((coordinateData i h - coordinateData i l) ^ 2 /
        ((waterCube d i r R).card : ℝ)) *
        ((C / (2 * (r : ℝ) + 1) ^ 3) *
          (2 * (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) *
            (1 + Real.log (2 * r + 1 : ℕ)))) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      rw [waterCube_face_height d i r R hl hh, card_waterCube]
      push_cast
      field_simp

/-- One actual product envelope bounds BOTH source observables. -/
theorem waterCube_aabb_le_of_productEnvelope {d : ℕ} (i : Fin d) (r R : ℕ)
    (p : unitInterval) {M : ℝ} (hM : 0 ≤ M)
    (henv : WaterCubeConnectionProductEnvelope i r R p M) :
    max (annealedRelaxed (waterCube d i r R) i (p:ℝ))
      (annealedB (waterCube d i r R) i (p:ℝ)) ≤
        2*(d:ℝ)*M*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2 := by
  obtain ⟨l,hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h,hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  exact max_le
    (annealedRelaxed_waterCube_le_of_productEnvelope i r R hl hh p hM henv)
    (annealedB_waterCube_le_of_productEnvelope i r R hl hh p hM henv)

/-- Explicit source-log conversion. The restriction h>=3 is essential:
log1=0 cannot bound a positive h1 energy. -/
lemma waterCube_one_add_log_le (r : ℕ) (hr : 1 ≤ r) :
    1+Real.log (2*r+1:ℕ) ≤ (1+1/Real.log 3)*Real.log (2*r+1:ℕ) := by
  have h3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log 3 ≤ Real.log (2*r+1:ℕ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 3 ≤ 2*r+1 by omega)
  have hratio := div_le_div_of_nonneg_right hlog h3.le
  rw [div_self h3.ne', div_eq_mul_inv] at hratio
  simp only [one_div]
  nlinarith

lemma waterCube_prior_prefactor_le_log (d r : ℕ) (hr : 1 ≤ r) {M : ℝ} (hM : 0 ≤ M) :
    2*(d:ℝ)*M*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2 ≤
      2*(d:ℝ)*(M*(1+1/Real.log 3))*Real.log (2*r+1:ℕ)/(2*(r:ℝ)+1)^2 := by
  have h := mul_le_mul_of_nonneg_left (waterCube_one_add_log_le r hr)
    (show 0 ≤ 2*(d:ℝ)*M by positivity)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith

/-- Literal logarithmic a- AND b-prior bounds, with ONE amplitude and decay
rate before all parameters, both regimes, and all odd heights h>=3.
The actual two-arm/product estimates are proved; only named STANDARD inputs
remain. This is homogeneous lem.aa_bound AND lem.bb_bound, not bulk/masked. -/
theorem waterCube_aabb_log_prior_of_standard_inputs {d : ℕ} (i : Fin d)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (p : unitInterval) (r R : ℕ), 1 ≤ r →
      ((criticalPoint d:ℝ) < (p:ℝ) →
        (p:ℝ) ≤ (criticalPoint d:ℝ)+(((2*r+1:ℕ):ℝ)^2)⁻¹ →
        max (annealedRelaxed (waterCube d i r R) i (p:ℝ))
          (annealedB (waterCube d i r R) i (p:ℝ)) ≤
            2*(d:ℝ)*M*Real.log (2*r+1:ℕ)/(2*(r:ℝ)+1)^2) ∧
      (p ≤ criticalPoint d →
        max (annealedRelaxed (waterCube d i r R) i (p:ℝ))
          (annealedB (waterCube d i r R) i (p:ℝ)) ≤
            (2*(d:ℝ)*M*Real.log (2*r+1:ℕ)/(2*(r:ℝ)+1)^2)*
              Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1))) := by
  obtain ⟨Mup,hMup,hup⟩ := waterCube_supercritical_prior_of_standard_inputs i hC
    hE hA hB hb hpc hpc1 ordinary criticalArm pioneers entropic
  obtain ⟨Mdown,c,hMdown,hc,hdown⟩ := waterCube_subcritical_prior_of_standard_inputs i
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  let M0 := max Mup Mdown
  have hM0 : 0 < M0 := lt_of_lt_of_le hMup (le_max_left _ _)
  let M := M0*(1+1/Real.log 3)
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M,c,hM,hc,?_⟩
  intro p r R hr
  constructor
  · intro hp hw
    apply (waterCube_aabb_le_of_productEnvelope i r R p hMup.le (hup p r R hp hw).1).trans
    exact (waterCube_prior_prefactor_mono d r (show Mup ≤ M0 from le_max_left _ _)).trans
      (waterCube_prior_prefactor_le_log d r hr hM0.le)
  · intro hp
    have henv := (hdown p r R hp).1
    have hbound := waterCube_aabb_le_of_productEnvelope i r R p (by positivity) henv
    calc
      _ ≤ (2*(d:ℝ)*Mdown*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2)*
          Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1)) := by
        convert hbound using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((waterCube_prior_prefactor_mono d r (show Mdown ≤ M0 from le_max_right _ _)).trans
          (waterCube_prior_prefactor_le_log d r hr hM0.le)) (Real.exp_nonneg _)

end NearCritical
