module
public import NearCritical.WaterCubeSubcriticalMiddle

/-! NEW subcritical lem.aa_bound: actual two-orientation product envelope and
harmonic energy deduction. No new arm/product/energy conclusion is assumed in
the final standard-input wrapper. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Modular NEW composition interface; the final theorem instantiates the
far-face field using the proved half-space extension. -/
theorem waterCube_productEnvelope_subcritical {d : ℕ} (i : Fin d)
    {C K G β c : ℝ} (hC : 1 ≤ C) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hβ : 0 ≤ β) (_hc : 0 ≤ c) (hcβ : c ≤ β/8)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (far : ∀ (p : unitInterval) (r R : ℕ) (upper : Bool)
      (x : DomainVertex (waterCube d i r R)),
      2 * waterCubeOppositeDepth i r upper x.val ≤ 2*r+1 → p ≤ criticalPoint d →
      (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
        K*((waterCubeOppositeDepth i r upper x.val+1:ℝ)/((2*r+1:ℕ):ℝ)^3)*
          Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*r+1:ℕ)))
    (p : unitInterval) (r R : ℕ) (hp : p ≤ criticalPoint d) :
    WaterCubeConnectionProductEnvelope i r R p
      ((16*C*K+16*(4*G+Real.exp (β/4))^2)*
        Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1))) := by
  intro e
  let D := waterCubeBaseDepth i r e.val.1
  let H : ℝ := 2*(r:ℝ)+1
  let q (upper : Bool) (x : DomainVertex (waterCube d i r R)) :=
    (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x)
  let t := (issuedNetwork (waterCube d i r R)).tail e
  let u := (issuedNetwork (waterCube d i r R)).head e
  have hH : 0 < H := by dsimp [H]; positivity
  have hheight : ((2*r+1 : ℕ) : ℝ) = H := by dsimp [H]; push_cast; ring
  have hD : (0 : ℝ) < D+1 := by positivity
  have hC0 : 0 ≤ C := by linarith
  let Z := Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*H)
  have hZ : 0 ≤ Z := Real.exp_nonneg _
  have hw : (p:ℝ) ≤ (criticalPoint d:ℝ) + (((2*r+1:ℕ):ℝ)^2)⁻¹ := by
    have hpc : (p:ℝ) ≤ (criticalPoint d:ℝ) := hp
    linarith [inv_nonneg.mpr (sq_nonneg (((2*r+1:ℕ):ℝ)))]
  have hnear : ∀ upper, q upper t ≤ 4*C/(D+1:ℝ)^2 ∧ q upper u ≤ 4*C/(D+1:ℝ)^2 := by
    intro upper
    have hd := waterCube_endpoint_target_ge_base i r R e upper
    constructor
    · apply (waterCube_face_probability_le_ordinary hC ordinary p i r R upper t hw).trans
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have h : (D:ℝ) ≤ waterCubeTargetDepth i r upper t.val := by exact_mod_cast hd.1
      nlinarith
    · apply (waterCube_face_probability_le_ordinary hC ordinary p i r R upper u hw).trans
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have h : (D:ℝ) ≤ waterCubeTargetDepth i r upper u.val := by exact_mod_cast hd.2
      nlinarith
  have heq : boundaryConnectionProducts (waterCube d i r R) i p e =
      q true t * q false u + q false t * q true u := by
    simp [q, t, u, boundaryConnectionProducts, waterCubeFaceConnectionEvent, add_comm]
  rw [heq]
  by_cases hmid : waterCubeLayer i r e.val.1 = r
  · have hmidbound := waterCube_middle_product_subcritical hG hβ subordinary p hp i r R e hmid
    rw [heq] at hmidbound
    have hdec : Real.exp (-(β/8)*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*H) ≤ Z := by
      apply Real.exp_le_exp.mpr
      have ht := Real.sqrt_nonneg ((criticalPoint d:ℝ)-(p:ℝ))
      nlinarith [mul_nonneg (sub_nonneg.mpr hcβ) (mul_nonneg ht hH.le)]
    have hcoef : 16*(4*G+Real.exp (β/4))^2/H^3 ≤
        (16*C*K+16*(4*G+Real.exp (β/4))^2)/H^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hC0 hK]
    calc
      _ ≤ (16*(4*G+Real.exp (β/4))^2/H^3)*(1/(D+1:ℝ))*
          Real.exp (-(β/8)*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*H) := hmidbound
      _ ≤ ((16*C*K+16*(4*G+Real.exp (β/4))^2)/H^3)*(1/(D+1:ℝ))*Z :=
        mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity)) hdec
          (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring
  · have hfar : ∃ upper, q upper t ≤ (2*K*(D+1:ℝ)/H^3)*Z ∧
        q upper u ≤ (2*K*(D+1:ℝ)/H^3)*Z := by
      let upper := decide (waterCubeLayer i r e.val.1 < r)
      have hcases : (upper = true ∧ waterCubeLayer i r e.val.1 < r) ∨
          (upper = false ∧ r < waterCubeLayer i r e.val.1) := by
        dsimp [upper]
        by_cases h : waterCubeLayer i r e.val.1 < r <;> simp [h]
        omega
      have ha := waterCube_far_amplitude_le i r R e upper hcases
      have hd := waterCube_endpoint_far_depths i r R e
      dsimp only at ha hd
      have hdep : 2*waterCubeOppositeDepth i r upper t.val ≤ 2*r+1 ∧
          2*waterCubeOppositeDepth i r upper u.val ≤ 2*r+1 := by
        rcases hcases with ⟨hu,h⟩ | ⟨hu,h⟩
        · rw [hu]; exact hd.1 h
        · rw [hu]; exact hd.2 h
      refine ⟨upper, ?_, ?_⟩
      · apply (far p r R upper t hdep.1 hp).trans
        have h : (waterCubeOppositeDepth i r upper t.val + 1 : ℝ) ≤ 2*(D+1:ℝ) := by exact_mod_cast ha.1
        rw [hheight]
        change _ * Z ≤ _
        calc
          _ ≤ (K * (2*(D+1:ℝ)/H^3))*Z :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (by positivity)) hK) hZ
          _ = _ := by ring
      · apply (far p r R upper u hdep.2 hp).trans
        have h : (waterCubeOppositeDepth i r upper u.val + 1 : ℝ) ≤ 2*(D+1:ℝ) := by exact_mod_cast ha.2
        rw [hheight]
        change _ * Z ≤ _
        calc
          _ ≤ (K * (2*(D+1:ℝ)/H^3))*Z :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (by positivity)) hK) hZ
          _ = _ := by ring
    obtain ⟨upper, ht, hu⟩ := hfar
    have hprod := two_orientation_product_le
      (show 0 ≤ q true t from measureReal_nonneg) (show 0 ≤ q true u from measureReal_nonneg)
      (show 0 ≤ q false t from measureReal_nonneg) (show 0 ≤ q false u from measureReal_nonneg)
      (by positivity : 0 ≤ 4*C/(D+1:ℝ)^2) (by positivity : 0 ≤ (2*K*(D+1:ℝ)/H^3)*Z)
      (hnear true).1 (hnear true).2 (hnear false).1 (hnear false).2
      (by cases upper; exact Or.inr ⟨ht,hu⟩; exact Or.inl ⟨ht,hu⟩)
    apply hprod.trans
    change 2*(4*C/(D+1:ℝ)^2)*((2*K*(D+1:ℝ)/H^3)*Z) ≤
      (((16*C*K+16*(4*G+Real.exp (β/4))^2)*Z)/H^3)*(1/(D+1:ℝ))
    field_simp
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (4*G+Real.exp (β/4))) hZ)
      (show 0 ≤ (D+1:ℝ)^2 by positivity)]

/-- NEW subcritical a-priori conductivity bound. The actual product envelope
and both face bounds are DISCHARGED; named STANDARD inputs alone remain.
One positive amplitude and rate precede all p,r,R, including p=0 and h=1. -/
theorem waterCube_subcritical_prior_of_standard_inputs {d : ℕ} (i : Fin d)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (p : unitInterval) (r R : ℕ), p ≤ criticalPoint d →
      WaterCubeConnectionProductEnvelope i r R p
        (M*Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1))) ∧
      annealedRelaxed (waterCube d i r R) i (p:ℝ) ≤
        (2*(d:ℝ)*M*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2)*
          Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1)) := by
  obtain ⟨K, cFar, hK, hcFar, hfar⟩ := waterCube_face_bounds_of_standard_inputs i
    hE hA hB hb hpc hpc1 criticalArm pioneers entropic
  let c := min cFar (β/8)
  have hc : 0 < c := lt_min hcFar (by positivity)
  let M := 16*C*K+16*(4*G+Real.exp (β/4))^2
  have hCpos : 0 < C := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hfar' : ∀ (p : unitInterval) (r R : ℕ) (upper : Bool)
      (x : DomainVertex (waterCube d i r R)),
      2*waterCubeOppositeDepth i r upper x.val ≤ 2*r+1 → p ≤ criticalPoint d →
      (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
        K*((waterCubeOppositeDepth i r upper x.val+1:ℝ)/((2*r+1:ℕ):ℝ)^3)*
          Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*r+1:ℕ)) := by
    intro p r R upper x hd hp
    apply ((hfar p r R upper x hd).2 hp).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have ht := Real.sqrt_nonneg ((criticalPoint d:ℝ)-(p:ℝ))
    have hrate : c ≤ cFar := min_le_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hrate)
      (mul_nonneg ht (Nat.cast_nonneg (2*r+1)))]
  refine ⟨M,c,hM,hc,?_⟩
  intro p r R hp
  have henv := waterCube_productEnvelope_subcritical i hC hK.le hG hβ.le hc.le
    (min_le_right _ _) ordinary subordinary hfar' p r R hp
  refine ⟨henv,?_⟩
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  calc
    _ ≤ 2*(d:ℝ)*(M*Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1)))*
        (1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2 :=
      annealedRelaxed_waterCube_le_of_productEnvelope i r R hl hh p (by positivity) henv
    _ = _ := by ring

/-- Monotonicity in the common amplitude, including the h=1 logarithm. -/
lemma waterCube_prior_prefactor_mono (d r : ℕ) {M N : ℝ} (hMN : M ≤ N) :
    2*(d:ℝ)*M*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2 ≤
      2*(d:ℝ)*N*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2 := by
  have hlog : 0 ≤ 1+Real.log (2*r+1:ℕ) := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ (2*r+1:ℕ) by exact_mod_cast (show 1 ≤ 2*r+1 by omega))
    linarith
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMN (by positivity)) hlog) (sq_nonneg _)

/-- BOTH branches of NEW lem.aa_bound for the actual finite cube, under named
STANDARD inputs only. One positive amplitude and decay rate are fixed before
all parameters and scales. `1+log h` retains h=1 explicitly. -/
theorem waterCube_prior_of_standard_inputs {d : ℕ} (i : Fin d)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (p : unitInterval) (r R : ℕ),
      ((criticalPoint d:ℝ) < (p:ℝ) →
        (p:ℝ) ≤ (criticalPoint d:ℝ)+(((2*r+1:ℕ):ℝ)^2)⁻¹ →
        annealedRelaxed (waterCube d i r R) i (p:ℝ) ≤
          2*(d:ℝ)*M*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2) ∧
      (p ≤ criticalPoint d →
        annealedRelaxed (waterCube d i r R) i (p:ℝ) ≤
          (2*(d:ℝ)*M*(1+Real.log (2*r+1:ℕ))/(2*(r:ℝ)+1)^2)*
            Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1))) := by
  obtain ⟨Mup, hMup, hup⟩ := waterCube_supercritical_prior_of_standard_inputs i hC
    hE hA hB hb hpc hpc1 ordinary criticalArm pioneers entropic
  obtain ⟨Mdown, c, hMdown, hc, hdown⟩ := waterCube_subcritical_prior_of_standard_inputs i
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  refine ⟨max Mup Mdown,c,lt_of_lt_of_le hMup (le_max_left _ _),hc,?_⟩
  intro p r R
  constructor
  · intro hp hw
    exact ((hup p r R hp hw).2).trans (waterCube_prior_prefactor_mono d r (le_max_left _ _))
  · intro hp
    exact ((hdown p r R hp).2).trans (mul_le_mul_of_nonneg_right
      (waterCube_prior_prefactor_mono d r (le_max_right _ _)) (Real.exp_nonneg _))

end NearCritical
