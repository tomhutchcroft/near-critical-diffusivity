module

public import NearCritical.Section9MiddleGeometry
public import NearCritical.Section9CoalescenceMass
public import NearCritical.Section9CoalescenceRestrictedBound
import Mathlib.Tactic.Linarith

@[expose] public section
namespace NearCritical
open scoped Classical

/-- The enumeration box gives a common finite mass radius for the
middle candidates, the right tube and the end-cube targets. -/
theorem section9_distance_le_of_mem_centeredBox {d n : ℕ} {x y : Vertex d}
    (hx : x ∈ centeredBox d (3*n)) (hy : y ∈ centeredBox d (3*n)) :
    latticeDistance x y ≤ ((6*n : ℕ) : ℝ) := by
  change dist (vertexReal x) (vertexReal y) ≤ _
  apply (dist_pi_le_iff (Nat.cast_nonneg _)).mpr
  intro j
  have hxj := mem_centeredBox.mp hx j
  have hyj := mem_centeredBox.mp hy j
  have hxlo : -(3*(n:ℝ)) ≤ (x j : ℝ) := by exact_mod_cast hxj.1
  have hxhi : (x j : ℝ) ≤ 3*(n:ℝ) := by exact_mod_cast hxj.2
  have hylo : -(3*(n:ℝ)) ≤ (y j : ℝ) := by exact_mod_cast hyj.1
  have hyhi : (y j : ℝ) ≤ 3*(n:ℝ) := by exact_mod_cast hyj.2
  change dist (x j : ℝ) (y j : ℝ) ≤ _
  rw [Real.dist_eq, Nat.cast_mul, Nat.cast_ofNat]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Both orientations of a restricted connection have the same probability. -/
theorem section9RightArm_symm {d : ℕ} (R : Finset (Vertex d)) (a b : Vertex d) :
    section9RightArm R a b = section9RightArm R b a := by
  suffices connectionToSetEvent (R : Set (Vertex d)) a {b} =
      connectionToSetEvent (R : Set (Vertex d)) b {a} by
    unfold section9RightArm
    rw [this]
  ext ω
  constructor <;> rintro ⟨hx, y, hy, hyR, hxy⟩
  · have h : y = b := hy
    subst y
    exact ⟨hyR, a, rfl, hx, hxy.symm⟩
  · have h : y = a := hy
    subst y
    exact ⟨hyR, b, rfl, hx, hxy.symm⟩

/-- The weighted pivot-head sum over the actual middle candidates has the
same quadratic bound as the Green mass, times the lattice degree. -/
theorem section9_middle_head_mass_le {d : ℕ} (hd : 2 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (i : Fin d) (n : ℕ) (R : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ centeredBox d (3*n)) :
    ∑ e ∈ orientedLatticePairs (section9FiniteMiddle i n), section9RightArm R u e.2 ≤
      (2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2)) := by
  refine (section9_oriented_head_mass_le (section9FiniteMiddle i n) (section9RightArm R u)
    (fun _ _ => MeasureTheory.measureReal_nonneg)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact section9_restricted_arm_mass_le hd hG green _ _ u (6*n) (fun x hx =>
    section9_distance_le_of_mem_centeredBox hu (Finset.mem_filter.mp hx).1)

end NearCritical
