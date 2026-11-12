module
public import NearCritical.WaterCubeSubcriticalArms
public import NearCritical.WaterCubeSupercriticalPrior

/-! The missing middle-layer exponential gain in source lem.aa_bound.
Uses ordinary subcritical arms at BOTH faces; no invalid half-space depth
condition is imposed at either endpoint. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Actual two-orientation product at a middle-layer bond, including h=1.
Only the named standard ordinary subcritical input is required. -/
theorem waterCube_middle_product_subcritical {d : ℕ} {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (ordinary : OrdinaryArmSubcriticalInput d C b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (i : Fin d) (r R : ℕ)
    (e : IssuedBond (waterCube d i r R)) (hmid : waterCubeLayer i r e.val.1 = r) :
    boundaryConnectionProducts (waterCube d i r R) i p e ≤
      (16*(4*C+Real.exp (b/4))^2/(2*(r:ℝ)+1)^3) *
        (1/(waterCubeBaseDepth i r e.val.1+1:ℝ)) *
          Real.exp (-(b/8)*Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))*(2*(r:ℝ)+1)) := by
  let P := 4*C+Real.exp (b/4)
  let H : ℝ := 2*(r:ℝ)+1
  let t := Real.sqrt ((criticalPoint d:ℝ)-(p:ℝ))
  let E := Real.exp (-(b/8)*t*H)
  let N := P/(r+1:ℝ)^2
  let q (upper : Bool) (x : DomainVertex (waterCube d i r R)) :=
    (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x)
  let v := (issuedNetwork (waterCube d i r R)).tail e
  let w := (issuedNetwork (waterCube d i r R)).head e
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hE1 : E ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hb ht) hH.le]
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hD : waterCubeBaseDepth i r e.val.1 = r := by
    unfold waterCubeBaseDepth
    rw [hmid]
    omega
  have hdepth := waterCube_middle_target_depths i r R e hmid
  have hbound : ∀ upper, q upper v ≤ N*E ∧ q upper w ≤ N*E := by
    intro upper
    have hx : ∀ (x : DomainVertex (waterCube d i r R)),
        r ≤ waterCubeTargetDepth i r upper x.val → q upper x ≤ N*E := by
      intro x hd
      have hm : (r:ℝ) ≤ waterCubeTargetDepth i r upper x.val := by exact_mod_cast hd
      have hc : P/(waterCubeTargetDepth i r upper x.val+1:ℝ)^2 ≤ N := by
        apply div_le_div_of_nonneg_left hP (by positivity)
        nlinarith
      have he : Real.exp (-(b/4)*t*(waterCubeTargetDepth i r upper x.val+1:ℝ)) ≤ E := by
        apply Real.exp_le_exp.mpr
        have ht : 0 ≤ t := Real.sqrt_nonneg _
        dsimp [H]
        nlinarith [mul_nonneg (mul_nonneg hb ht) (show 0 ≤ (waterCubeTargetDepth i r upper x.val:ℝ)-(r:ℝ) by linarith)]
      exact (waterCube_face_subcritical_padded hC hb ordinary p hp i r R upper x).trans
        (mul_le_mul hc he (Real.exp_nonneg _) hN)
    exact ⟨hx v (hdepth upper).1, hx w (hdepth upper).2⟩
  have hprod := two_orientation_product_le
    (show 0 ≤ q true v from measureReal_nonneg) (show 0 ≤ q true w from measureReal_nonneg)
    (show 0 ≤ q false v from measureReal_nonneg) (show 0 ≤ q false w from measureReal_nonneg)
    (mul_nonneg hN hE) (mul_nonneg hN hE)
    (hbound true).1 (hbound true).2 (hbound false).1 (hbound false).2
    (Or.inl ⟨(hbound true).1,(hbound true).2⟩)
  have heq : boundaryConnectionProducts (waterCube d i r R) i p e =
      q true v*q false w+q false v*q true w := by
    simp [q,v,w,boundaryConnectionProducts,waterCubeFaceConnectionEvent,add_comm]
  rw [heq, hD]
  change _ ≤ (16*P^2/H^3)*(1/(r+1:ℝ))*E
  have hscale : H^3 ≤ 8*(r+1:ℝ)^3 := by dsimp [H]; nlinarith [sq_nonneg (r:ℝ)]
  have hcoef : 2*N*N ≤ (16*P^2/H^3)*(1/(r+1:ℝ)) := by
    dsimp [N]
    have hm := mul_le_mul_of_nonneg_left hscale (sq_nonneg P)
    field_simp
    nlinarith
  calc
    _ ≤ 2*(N*E)*(N*E) := hprod
    _ ≤ (2*N*N)*E := by
      have he2 : E*E ≤ E := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left he2 (show 0 ≤ 2*N*N by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

end NearCritical
