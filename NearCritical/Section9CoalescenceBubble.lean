module

public import NearCritical.Section8Convolution
public import NearCritical.ThreePointDiagram
public import NearCritical.ConnectionToSet

@[expose] public section
namespace NearCritical
open MeasureTheory

/-- Finite critical bubble estimate for the shared-left diagram, including
coincident roots. The bound is uniform in the branch-vertex cutoff. -/
theorem section9_finite_bubble_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (L : Finset (Vertex d)) (x y : Vertex d) :
    ∑ u ∈ L, twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) y u ≤
      G^2 * (((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
        (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) := by
  calc
    _ ≤ ∑ u ∈ L, G^2 *
        ((max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ)) *
          (max 1 (latticeDistance y u))^((2 : ℝ)-(d : ℝ))) := by
      apply Finset.sum_le_sum
      intro u _
      calc
        _ ≤ (G * (max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ))) *
            (G * (max 1 (latticeDistance y u))^((2 : ℝ)-(d : ℝ))) :=
          mul_le_mul (green x u) (green y u) (by exact MeasureTheory.measureReal_nonneg)
            (by positivity)
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg G)
      simpa only [Nat.cast_one] using
        Section8.truncated_green_convolution_le hd 1 (by decide) L x y

/-- The finite bubble bound applies to the actual restricted arms in
the Case 1 diagram. -/
theorem section9_restricted_bubble_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (L : Finset (Vertex d)) (x y : Vertex d) :
    let P := fun a b => (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    ∑ u ∈ L, P x u * P y u ≤
      G^2 * (((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
        (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) := by
  intro P
  have hP (a b : Vertex d) : P a b ≤ twoPoint d (criticalPoint d) a b := by
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro ω ⟨_, v, hv, _, hab⟩
    have hvb : v = b := hv
    subst v
    have hle : restrictedGraph ω (L : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    exact hab.mono hle
  calc
    _ ≤ ∑ u ∈ L, twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) y u :=
      Finset.sum_le_sum fun u _ => mul_le_mul (hP x u) (hP y u)
        measureReal_nonneg measureReal_nonneg
    _ ≤ _ := section9_finite_bubble_le hd hG green L x y

end NearCritical
