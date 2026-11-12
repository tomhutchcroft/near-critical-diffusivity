module
public import NearCritical.Section8ExtensionDeletionCost
public import NearCritical.Section9CoalescenceBubble
public import NearCritical.NestRegularBoundary

/-! Actual first regularity-energy error for outward unique extension. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Moving outward from a supporting coordinate wall increases every
supremum distance to a point behind the wall, by at least the shift length. -/
theorem section8_outward_shift_distance_lower {d : ℕ}
    (x y : Vertex d) (i : Fin d) (r : ℕ) (hy : y i ≤ x i) :
    max (r : ℝ) (latticeDistance x y) ≤
      latticeDistance (Function.update x i (x i+(r : ℤ))) y := by
  let a := Function.update x i (x i+(r : ℤ))
  have hyR : (y i : ℝ) ≤ (x i : ℝ) := by exact_mod_cast hy
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ha : (a i : ℝ) = (x i : ℝ)+(r : ℝ) := by
    simp [a]
  have hcoord (j : Fin d) : |(x j : ℝ)-(y j : ℝ)| ≤ |(a j : ℝ)-(y j : ℝ)| := by
    by_cases hj : j = i
    · subst j
      rw [ha,abs_of_nonneg (sub_nonneg.mpr hyR),abs_of_nonneg (by linarith)]
      linarith
    · simp [a,hj]
  have hxy : latticeDistance x y ≤ latticeDistance a y := by
    change dist (vertexReal x) (vertexReal y) ≤ latticeDistance a y
    apply (dist_pi_le_iff (latticeDistance_nonneg a y)).mpr
    intro j
    have hproj : |(a j : ℝ)-(y j : ℝ)| ≤ latticeDistance a y := by
      simpa only [latticeDistance,vertexReal,Real.dist_eq] using
        dist_le_pi_dist (vertexReal a) (vertexReal y) j
    change dist (x j : ℝ) (y j : ℝ) ≤ latticeDistance a y
    rw [Real.dist_eq]
    exact (hcoord j).trans hproj
  have hr : (r : ℝ) ≤ latticeDistance a y := by
    have hproj : |(a i : ℝ)-(y i : ℝ)| ≤ latticeDistance a y := by
      simpa only [latticeDistance,vertexReal,Real.dist_eq] using
        dist_le_pi_dist (vertexReal a) (vertexReal y) i
    rw [ha,abs_of_nonneg (by linarith)] at hproj
    linarith
  exact max_le hr hxy

/-- The shifted clipped kernel is bounded by the exact regularity kernel,
for every nonpositive exponent and every positive integer clipping radius. -/
theorem section8_outward_shift_kernel_le {d : ℕ}
    (x y : Vertex d) (i : Fin d) (r : ℕ) (hr : 1 ≤ r) (hy : y i ≤ x i)
    (q : ℝ) (hq : q ≤ 0) :
    (max 1 (latticeDistance (Function.update x i (x i+(r : ℤ))) y))^q ≤
      (max (r : ℝ) (latticeDistance x y))^q := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  exact Real.rpow_le_rpow_of_nonpos
    (zero_lt_one.trans_le (hrR.trans (le_max_left _ _)))
    ((section8_outward_shift_distance_lower x y i r hy).trans (le_max_right _ _)) hq

/-- Actual restricted-arm deletion products are controlled by the literal
ERE1 sum. Geometric assumptions describe the wall, target separation and
small-cube exclusion; no probability or energy estimate is assumed. -/
theorem section8_extension_deletion_ere_one_le {d : ℕ} (hd : 2 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (T F S : Finset (Vertex d)) (x z : Vertex d) (i : Fin d) (r : ℕ) (hr : 1 ≤ r)
    (n : ℝ) (hn : 0 < n) (hwall : ∀ y ∈ F, y i ≤ x i)
    (hsep : ∀ y ∈ F ∩ T, n/4 ≤ latticeDistance y z) (hTS : Disjoint T S) :
    (∑ y ∈ F ∩ T,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (T : Set (Vertex d)) (Function.update x i (x i+(r : ℤ))) {y}) *
      (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) y {z})) ≤
      (G^2*(4 : ℝ)^((d : ℝ)-2))*n^((2 : ℝ)-(d : ℝ))*regularityEnergyOne F S r x := by
  let q : ℝ := 2-(d : ℝ)
  let a := Function.update x i (x i+(r : ℤ))
  let w := fun y : Vertex d => (max (r : ℝ) (latticeDistance x y))^((2 : ℤ)-(d : ℤ))
  let K : ℝ := (G^2*(4 : ℝ)^((d : ℝ)-2))*n^q
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : q ≤ 0 := by dsimp [q]; linarith
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hw (y : Vertex d) : 0 ≤ w y :=
    zpow_nonneg (zero_le_one.trans (hrR.trans (le_max_left _ _))) _
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (sq_nonneg G) (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hn.le _)
  have hpower (y : Vertex d) : (max (r : ℝ) (latticeDistance x y))^q = w y := by
    simpa only [w,q,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast] using
      Real.rpow_intCast (max (r : ℝ) (latticeDistance x y)) ((2 : ℤ)-(d : ℤ))
  have hdiv : (n/4)^q = n^q*(4 : ℝ)^((d : ℝ)-2) := by
    rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 4),div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    have he : -q = (d : ℝ)-2 := by dsimp [q]; ring
    rw [he]
  have hDom (u v : Vertex d) :
      (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) u {v}) ≤
        twoPoint d (criticalPoint d) u v := by
    change (percolation d (criticalPoint d)).real
      (connectionToSetEvent (T : Set (Vertex d)) u {v}) ≤
      (percolation d (criticalPoint d)).real (connectionEvent u v)
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro ω ⟨_,t,ht,_,hut⟩
    have htv : t = v := ht
    subst t
    have hle : restrictedGraph ω (T : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    exact hut.mono hle
  have heach (y : Vertex d) (hy : y ∈ F ∩ T) :
      (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) a {y}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) y {z}) ≤
      K*w y := by
    have hA : twoPoint d (criticalPoint d) a y ≤ G*w y :=
      (green a y).trans ((mul_le_mul_of_nonneg_left
        (section8_outward_shift_kernel_le x y i r hr (hwall y (Finset.mem_inter.mp hy).1) q hq) hG).trans_eq
          (by rw [hpower]))
    have hB : twoPoint d (criticalPoint d) y z ≤ G*(n/4)^q :=
      (green y z).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity)
          ((hsep y hy).trans (le_max_right _ _)) hq) hG)
    calc
      _ ≤ (G*w y)*(G*(n/4)^q) := mul_le_mul
        ((hDom a y).trans hA) ((hDom y z).trans hB) measureReal_nonneg (mul_nonneg hG (hw y))
      _ = _ := by rw [hdiv]; dsimp [K]; ring
  have hsub : F ∩ T ⊆ F \ S := by
    intro y hy
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hy).1,
      fun hyS => Finset.disjoint_left.mp hTS (Finset.mem_inter.mp hy).2 hyS⟩
  calc
    _ ≤ ∑ y ∈ F ∩ T, K*w y := Finset.sum_le_sum fun y hy => heach y hy
    _ = K*(∑ y ∈ F ∩ T, w y) := (Finset.mul_sum _ _ _).symm
    _ ≤ K*(∑ y ∈ F \ S, w y) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hw y)) hK
    _ = _ := rfl

end NearCritical
