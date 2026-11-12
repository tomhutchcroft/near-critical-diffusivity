module

public import NearCritical.WaterCubeLayerSum
public import NearCritical.SourceConnectionBounds

/-! The harmonic summation part of source lem.aa_bound. The face-connection
product envelope below is an UNRESOLVED NEW probability/geometry input, not a
standard literature theorem and not an established premise of this development. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- Unresolved new input: a bound on the actual two-orientation BK products.
The depth is a base-coordinate proxy; relating face connections to this proxy
is part of the missing probability argument. -/
def WaterCubeConnectionProductEnvelope {d : ℕ} (i : Fin d) (r R : ℕ)
    (p : unitInterval) (C : ℝ) : Prop :=
  ∀ e : IssuedBond (waterCube d i r R),
    boundaryConnectionProducts (waterCube d i r R) i p e ≤
      (C / (2 * (r : ℝ) + 1) ^ 3) *
        (1 / (waterCubeBaseDepth i r e.val.1 + 1 : ℝ))

/-- Conditional completion of the issued-edge summation in eq.aa_bound_step2.
The harmless `1 + log h` retains the degenerate h=1 cube explicitly. -/
theorem annealedRelaxed_waterCube_le_of_productEnvelope {d : ℕ} (i : Fin d)
    (r R : ℕ) {l h : DomainVertex (waterCube d i r R)}
    (hl : l ∈ negativeFace (waterCube d i r R) i)
    (hh : h ∈ positiveFace (waterCube d i r R) i)
    (p : unitInterval) {C : ℝ} (hC : 0 ≤ C)
    (henv : WaterCubeConnectionProductEnvelope i r R p C) :
    annealedRelaxed (waterCube d i r R) i (p : ℝ) ≤
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
      annealedRelaxed_le_connectionProducts _ i hl hh p
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

end NearCritical
