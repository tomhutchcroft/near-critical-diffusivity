module
public import NearCritical.WaterCubeEndpointDepths
public import NearCritical.WaterCubePriorBound

/-! NEW supercritical branch of lem.aa_bound from actual finite-face events.
Both orientations are retained; midpoint bonds use ordinary arms only. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

lemma waterCube_endpoint_target_ge_base {d : ℕ} (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R)) (upper : Bool) :
    waterCubeBaseDepth i r e.val.1 ≤ waterCubeTargetDepth i r upper
      ((issuedNetwork (waterCube d i r R)).tail e).val ∧
    waterCubeBaseDepth i r e.val.1 ≤ waterCubeTargetDepth i r upper
      ((issuedNetwork (waterCube d i r R)).head e).val := by
  have hd := waterCube_endpoint_depths i r R e
  dsimp only at hd
  have hs := waterCubeDirectionStep_le_one i e
  have hk := waterCubeLayer_lt i r R (Finset.mem_product.mp e.property).1
  unfold waterCubeBaseDepth
  cases upper <;> simp only [waterCubeTargetDepth, Bool.not_true, Bool.not_false] <;> omega

lemma waterCube_far_amplitude_le {d : ℕ} (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R)) :
    let k := waterCubeLayer i r e.val.1
    let D := waterCubeBaseDepth i r e.val.1
    ∀ upper : Bool, (upper = true ∧ k < r) ∨ (upper = false ∧ r < k) →
      waterCubeOppositeDepth i r upper ((issuedNetwork (waterCube d i r R)).tail e).val + 1 ≤ 2 * (D + 1) ∧
      waterCubeOppositeDepth i r upper ((issuedNetwork (waterCube d i r R)).head e).val + 1 ≤ 2 * (D + 1) := by
  dsimp only
  have hd := waterCube_endpoint_depths i r R e
  dsimp only at hd
  have hs := waterCubeDirectionStep_le_one i e
  have hk := waterCubeLayer_lt i r R (Finset.mem_product.mp e.property).1
  intro upper hu
  unfold waterCubeBaseDepth
  rcases hu with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

lemma two_orientation_product_le {a b c d N F : ℝ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) (hd : 0 ≤ d)
    (hN : 0 ≤ N) (hF : 0 ≤ F)
    (han : a ≤ N) (hbn : b ≤ N) (hcn : c ≤ N) (hdn : d ≤ N)
    (hfar : (a ≤ F ∧ b ≤ F) ∨ (c ≤ F ∧ d ≤ F)) :
    a * d + c * b ≤ 2 * N * F := by
  rcases hfar with h | h
  · nlinarith [mul_le_mul h.1 hdn hd hF, mul_le_mul hcn h.2 hb hN]
  · nlinarith [mul_le_mul han h.2 hd hN, mul_le_mul h.1 hbn hb hF]

/-- The actual two-orientation envelope, with a fixed quantitative half-space
bound supplied by the proved extension. This intermediate interface is NEW;
the final theorem below instantiates it from named standard inputs. -/
theorem waterCube_productEnvelope_supercritical {d : ℕ} (i : Fin d)
    {C K : ℝ} (hC : 1 ≤ C) (hK : 0 ≤ K)
    (ordinary : OrdinaryArmWindowInput d C)
    (far : ∀ (p : unitInterval) (r R : ℕ) (upper : Bool)
      (x : DomainVertex (waterCube d i r R)),
      2 * waterCubeOppositeDepth i r upper x.val ≤ 2 * r + 1 →
      (criticalPoint d : ℝ) < (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ) + (((2 * r + 1 : ℕ) : ℝ)^2)⁻¹ →
      (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
        K * ((waterCubeOppositeDepth i r upper x.val + 1 : ℝ) /
          ((2 * r + 1 : ℕ) : ℝ)^3))
    (p : unitInterval) (r R : ℕ) (hp : (criticalPoint d : ℝ) < (p : ℝ))
    (hw : (p : ℝ) ≤ (criticalPoint d : ℝ) + (((2 * r + 1 : ℕ) : ℝ)^2)⁻¹) :
    WaterCubeConnectionProductEnvelope i r R p (16*C*K + 256*C^2) := by
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
  · have hDr : D = r := by dsimp [D, waterCubeBaseDepth]; rw [hmid]; omega
    have hprod := two_orientation_product_le
      (show 0 ≤ q true t from measureReal_nonneg) (show 0 ≤ q true u from measureReal_nonneg)
      (show 0 ≤ q false t from measureReal_nonneg) (show 0 ≤ q false u from measureReal_nonneg)
      (by positivity : 0 ≤ 4*C/(D+1:ℝ)^2) (by positivity : 0 ≤ 4*C/(D+1:ℝ)^2)
      (hnear true).1 (hnear true).2 (hnear false).1 (hnear false).2
      (Or.inl ⟨(hnear true).1, (hnear true).2⟩)
    apply hprod.trans
    change 2*(4*C/(D+1:ℝ)^2)*(4*C/(D+1:ℝ)^2) ≤
      ((16*C*K+256*C^2)/H^3)*(1/(D+1:ℝ))
    have hscale : H^3 ≤ 8*(D+1:ℝ)^3 := by rw [hDr]; dsimp [H]; nlinarith [sq_nonneg (r:ℝ)]
    have hm := mul_le_mul_of_nonneg_left hscale (sq_nonneg C)
    field_simp
    nlinarith [mul_nonneg (mul_nonneg hC0 hK) (show 0 ≤ (D+1:ℝ)^3 by positivity)]
  · have hfar : ∃ upper, q upper t ≤ 2*K*(D+1:ℝ)/H^3 ∧
        q upper u ≤ 2*K*(D+1:ℝ)/H^3 := by
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
      · apply (far p r R upper t hdep.1 hp hw).trans
        have h : (waterCubeOppositeDepth i r upper t.val + 1 : ℝ) ≤ 2*(D+1:ℝ) := by exact_mod_cast ha.1
        rw [hheight]
        calc
          _ ≤ K * (2*(D+1:ℝ)/H^3) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (by positivity)) hK
          _ = _ := by ring
      · apply (far p r R upper u hdep.2 hp hw).trans
        have h : (waterCubeOppositeDepth i r upper u.val + 1 : ℝ) ≤ 2*(D+1:ℝ) := by exact_mod_cast ha.2
        rw [hheight]
        calc
          _ ≤ K * (2*(D+1:ℝ)/H^3) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (by positivity)) hK
          _ = _ := by ring
    obtain ⟨upper, ht, hu⟩ := hfar
    have hprod := two_orientation_product_le
      (show 0 ≤ q true t from measureReal_nonneg) (show 0 ≤ q true u from measureReal_nonneg)
      (show 0 ≤ q false t from measureReal_nonneg) (show 0 ≤ q false u from measureReal_nonneg)
      (by positivity : 0 ≤ 4*C/(D+1:ℝ)^2) (by positivity : 0 ≤ 2*K*(D+1:ℝ)/H^3)
      (hnear true).1 (hnear true).2 (hnear false).1 (hnear false).2
      (by cases upper; exact Or.inr ⟨ht,hu⟩; exact Or.inl ⟨ht,hu⟩)
    apply hprod.trans
    change 2*(4*C/(D+1:ℝ)^2)*(2*K*(D+1:ℝ)/H^3) ≤
      ((16*C*K+256*C^2)/H^3)*(1/(D+1:ℝ))
    field_simp
    nlinarith [mul_nonneg (sq_nonneg C) (show 0 ≤ (D+1:ℝ)^2 by positivity)]

/-- NEW supercritical a-priori conductivity bound, with the product envelope
DISCHARGED. Constants precede all parameters/scales; only cited STANDARD
ordinary-arm/L1/weighted-L2/finite-DM inputs and pc nontriviality remain. -/
theorem waterCube_supercritical_prior_of_standard_inputs {d : ℕ} (i : Fin d)
    {C E A B b : ℝ} (hC : 1 ≤ C) (hE : 0 < E) (hA : 0 < A)
    (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ M : ℝ, 0 < M ∧ ∀ (p : unitInterval) (r R : ℕ),
      (criticalPoint d : ℝ) < (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ) + (((2*r+1 : ℕ) : ℝ)^2)⁻¹ →
      WaterCubeConnectionProductEnvelope i r R p M ∧
      annealedRelaxed (waterCube d i r R) i (p : ℝ) ≤
        2*(d:ℝ)*M*(1+Real.log (2*r+1 : ℕ))/(2*(r:ℝ)+1)^2 := by
  obtain ⟨K, c, hK, _, hfar⟩ := waterCube_face_bounds_of_standard_inputs i
    hE hA hB hb hpc hpc1 criticalArm pioneers entropic
  let M := 16*C*K + 256*C^2
  have hCpos : 0 < C := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro p r R hp hw
  have henv := waterCube_productEnvelope_supercritical i hC hK.le ordinary
    (fun p r R upper x hd hp hw => (hfar p r R upper x hd).1 hp hw) p r R hp hw
  refine ⟨henv, ?_⟩
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  exact annealedRelaxed_waterCube_le_of_productEnvelope i r R hl hh p hM.le henv

end NearCritical
