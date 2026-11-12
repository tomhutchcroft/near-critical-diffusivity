module
public import NearCritical.Section8HeartUpper

/-! Uniform quantitative PxinfC upper scaling at admissible integer radii. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private lemma one_sub_rpow {d : ℕ} (hd : 1 ≤ d) (t : ℝ) (ht : 0 < t) :
    t^((1 : ℝ)-(d : ℝ)) = 1/t^(d-1) := by
  have he : (1 : ℝ)-(d : ℝ) = -((d-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [he,Real.rpow_neg ht.le,Real.rpow_natCast]
  simp

/-- Uniform integer-radius heart-membership upper rate. All geometric and
probability factors in the preceding bound are discharged. -/
theorem cube_boundary_heart_probability_scaled {d N H : ℕ} (hd : 4 ≤ d)
    (hH : 1 ≤ H) (hHN : 4*H ≤ N) (heart : Finset (Vertex d))
    (hheart : heart ⊆ centeredBox d H) (x : Vertex d)
    (hx : x ∈ boundarySites (centeredBox d N)) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B) :
    (percolation d (criticalPoint d)).real
      {ω | x ∈ heartClusterUnion ω (centeredBox d N) heart} ≤
      ((2*C)*2^(d-1)*B*(2*(d : ℝ)*5^(d-1)))*(H : ℝ)^(d-4)/(N : ℝ)^(d-1) := by
  have hHR : H < 2*H := by omega
  have hRN : 2*H < N := by omega
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hscale : 4*(H : ℝ) ≤ N := by exact_mod_cast hHN
  have hgap : (N : ℝ)/2 ≤ max 1 ((N : ℝ)-(2*H : ℕ)) := by
    have hh := le_max_right 1 ((N : ℝ)-(2*H : ℕ))
    push_cast at hh ⊢
    linarith
  have hprefix : (2*C)*(max 1 ((N : ℝ)-(2*H : ℕ)))^((1 : ℝ)-(d : ℝ)) ≤
      ((2*C)*2^(d-1))/(N : ℝ)^(d-1) := by
    have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (N : ℝ)/2) hgap
      (show (1 : ℝ)-(d : ℝ) ≤ 0 by linarith)
    calc
      _ ≤ (2*C)*((N : ℝ)/2)^((1 : ℝ)-(d : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by
        rw [one_sub_rpow (by omega : 1 ≤ d) _ (by positivity),div_pow]
        field_simp [ne_of_gt hNpos]
        <;> ring
  have hcard : ((2*d*(2*(2*H)+1)^(d-1) : ℕ) : ℝ) ≤
      (2*(d : ℝ)*5^(d-1))*(H : ℝ)^(d-1) := by
    have hp : (4*(H : ℝ)+1)^(d-1) ≤ (5*(H : ℝ))^(d-1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ = (2*(d : ℝ))*(4*(H : ℝ)+1)^(d-1) := by
        push_cast
        rw [show (2 : ℝ)*(2*(H : ℝ))+1 = 4*(H : ℝ)+1 by ring]
      _ ≤ (2*(d : ℝ))*(5*(H : ℝ))^(d-1) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have hgapNat : 2*H-H = H := by omega
  have hp := cube_boundary_heart_probability_le (by omega : 1 ≤ d) hHR hRN heart hheart x hx C B hC hB panis arm
  rw [hgapNat] at hp
  have hnum : (H : ℝ)^(d-1) = (H : ℝ)^(d-4)*(H : ℝ)^3 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ _ := hp
    _ ≤ (((2*C)*2^(d-1))/(N : ℝ)^(d-1)*(B/(H : ℝ)^3))*
        ((2*(d : ℝ)*5^(d-1))*(H : ℝ)^(d-1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hprefix (by positivity)) hcard (by positivity) (by positivity)
    _ = _ := by
      rw [hnum]
      field_simp [ne_of_gt hHpos,ne_of_gt hNpos]
      <;> ring

/-- Source rho^(d-4)n^-3 upper rate, with its actual admissible rounded-scale
conditions explicit. The same amplitude precedes every rho, H and N. -/
theorem cube_boundary_heart_probability_rho_le {d N H : ℕ} (hd : 4 ≤ d)
    (hH : 1 ≤ H) (hHN : 4*H ≤ N) (rho : ℝ) (hrho : 0 ≤ rho)
    (hround : (H : ℝ) ≤ rho*(N : ℝ)) (heart : Finset (Vertex d))
    (hheart : heart ⊆ centeredBox d H) (x : Vertex d)
    (hx : x ∈ boundarySites (centeredBox d N)) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B) :
    (percolation d (criticalPoint d)).real
      {ω | x ∈ heartClusterUnion ω (centeredBox d N) heart} ≤
      ((2*C)*2^(d-1)*B*(2*(d : ℝ)*5^(d-1)))*rho^(d-4)/(N : ℝ)^3 := by
  let K : ℝ := (2*C)*2^(d-1)*B*(2*(d : ℝ)*5^(d-1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (H : ℝ)^(d-4) ≤ (rho*(N : ℝ))^(d-4) :=
    pow_le_pow_left₀ (Nat.cast_nonneg H) hround _
  have he : (N : ℝ)^(d-1) = (N : ℝ)^(d-4)*(N : ℝ)^3 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ K*(H : ℝ)^(d-4)/(N : ℝ)^(d-1) :=
      cube_boundary_heart_probability_scaled hd hH hHN heart hheart x hx C B hC hB panis arm
    _ ≤ K*(rho*(N : ℝ))^(d-4)/(N : ℝ)^(d-1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK) (by positivity)
    _ = _ := by
      rw [mul_pow,he]
      dsimp [K]
      field_simp [ne_of_gt hNpos]
      <;> ring

end NearCritical.Section8
