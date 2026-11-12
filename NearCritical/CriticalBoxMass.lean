module

public import NearCritical.LatticeShells

/-! Source prop.num_spanning_new spatial two-point sum from actual assumption(A).
Reuses the established global Green bound and surface-order lattice shell sum. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- Uniform actual critical mass for any finite set of displacements in a
radius-R cube. The one constant is chosen before all sets, centers and radii. -/
theorem critical_twoPoint_mass_of_displacements {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℕ) (Z : Finset (Vertex d)) (u : Vertex d),
      (∀ s ∈ Z, s-u ∈ latticeSupCube d R) →
      (∑ s ∈ Z, twoPoint d (criticalPoint d) s u) ≤ K*(R+1:ℝ)^2 := by
  obtain ⟨C, hC, hgreen⟩ := critical_twoPoint_global_upper hd hA
  let D : ℝ := 2*(d:ℝ)*3^(d-1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C*(1+D), by positivity, ?_⟩
  intro R Z u hZ
  let w : Vertex d → ℝ := fun x => (max 1 (euclideanNorm x))^((2:ℝ)-(d:ℝ))
  have hi : Set.InjOn (fun s : Vertex d => s-u) (Z : Set (Vertex d)) := by
    intro x _hx y _hy hxy
    have h := congrArg (fun z : Vertex d => z+u) hxy
    simpa only [sub_add_cancel] using h
  have himage : Z.image (fun s => s-u) ⊆ latticeSupCube d R := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact hZ s hs
  have hw : (∑ s ∈ Z, w (s-u)) ≤ ∑ x ∈ latticeSupCube d R, w x := by
    calc
      _ = ∑ x ∈ Z.image (fun s => s-u), w x := (Finset.sum_image hi).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun x _hx _hn => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hR : (1:ℝ) ≤ (R+1:ℝ)^2 := by
    have hn : (0:ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith
  calc
    _ ≤ ∑ s ∈ Z, C*w (s-u) := Finset.sum_le_sum (fun s _hs => hgreen s u)
    _ = C*(∑ s ∈ Z, w (s-u)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*(∑ x ∈ latticeSupCube d R, w x) := mul_le_mul_of_nonneg_left hw hC.le
    _ ≤ C*(1+D*(R+1:ℝ)^2) := mul_le_mul_of_nonneg_left
      (sum_latticeSupCube_green_le hd R) hC.le
    _ ≤ C*((1+D)*(R+1:ℝ)^2) := mul_le_mul_of_nonneg_left (by nlinarith) hC.le
    _ = _ := by ring

/-- Same-cube endpoints have displacements in the doubled-radius cube. -/
lemma sub_mem_latticeSupCube_double {d N : ℕ} {s u : Vertex d}
    (hs : s ∈ latticeSupCube d N) (hu : u ∈ latticeSupCube d N) :
    s-u ∈ latticeSupCube d (2*N) := by
  apply mem_latticeSupCube.mpr
  intro i
  have ht : |s i-u i| ≤ |s i|+|u i| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (s i) 0 (u i)
  calc
    |(s-u) i| ≤ |s i|+|u i| := ht
    _ ≤ (N:ℤ)+(N:ℤ) := add_le_add (mem_latticeSupCube.mp hs i) (mem_latticeSupCube.mp hu i)
    _ = (2*N:ℕ) := by push_cast; ring

/-- Actual critical spatial input for the count-variance deduction. No spatial
sum, convolution or susceptibility estimate is an additional premise. -/
theorem critical_twoPoint_mass_in_sup_cube {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ latticeSupCube d N →
      ∀ u ∈ latticeSupCube d N,
        (∑ s ∈ Z, twoPoint d (criticalPoint d) s u) ≤ K*(N+1:ℝ)^2 := by
  obtain ⟨K, hK, hb⟩ := critical_twoPoint_mass_of_displacements hd hA
  refine ⟨4*K, by positivity, ?_⟩
  intro N Z hZ u hu
  have h := hb (2*N) Z u (fun s hs => sub_mem_latticeSupCube_double (hZ hs) hu)
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hs : (2*(N:ℝ)+1)^2 ≤ 4*(N+1:ℝ)^2 := by nlinarith
  calc
    _ ≤ K*(2*(N:ℝ)+1)^2 := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    _ ≤ K*(4*(N+1:ℝ)^2) := mul_le_mul_of_nonneg_left hs hK.le
    _ = _ := by ring

lemma centeredBox_eq_latticeSupCube (d N : ℕ) : centeredBox d N = latticeSupCube d N := by
  ext x
  simp only [mem_centeredBox, mem_latticeSupCube, abs_le]

/-- Literal existing odd-box convention: ONE constant uniformly controls the
actual critical mass over every finite root set in the centered box. -/
theorem critical_twoPoint_mass_in_centered_box {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      ∀ u ∈ centeredBox d N,
        (∑ s ∈ Z, twoPoint d (criticalPoint d) s u) ≤ K*(N+1:ℝ)^2 := by
  simpa only [centeredBox_eq_latticeSupCube] using critical_twoPoint_mass_in_sup_cube hd hA

end NearCritical
