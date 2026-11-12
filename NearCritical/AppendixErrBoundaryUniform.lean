module

public import NearCritical.AppendixErrClusterUniform

/-! The Appendix A boundary error, with the three branch regions summed on
a single transverse face. -/
@[expose] public section
noncomputable section
namespace NearCritical
open AppendixVariance MeasureTheory Section8
open scoped Classical

/-- Repackage the three branch regions into the root and target scales
used in the face sum. Both coefficients depend only on dimension. -/
theorem box_pair_branch_sum_scaled {d : ℕ} (hd : 7 ≤ d) :
    ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧
      ∀ (x w w' : Vertex d) (ℓ : Vertex d → ℕ) (h k : ℕ),
        1 ≤ h → 1 ≤ k → h ≤ linfDist x w → h ≤ linfDist x w' → k ≤ linfDist w w' →
        (∀ u, ℓ u ≤ 1 + min (linfDist x u) (min (linfDist u w) (linfDist u w'))) →
        ∀ (c : Vertex d) (K : ℕ),
        (∑ u ∈ linfBall c (K : ℤ), ((ℓ u + 1 : ℕ) : ℝ) ^ 3 /
          (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d *
            ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)) ≤
          X / ((h : ℝ) + 1) ^ (2 * d - 3) +
            Y / (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ (d - 3)) := by
  let S : ℝ := 2 * (d : ℝ) * 3 ^ (d - 1)
  let e := 2 * d - 3
  let f := d - 3
  let X : ℝ := 2 ^ (2 * d + 3) * S + 8 * S * (((e : ℝ) + 1) / (e : ℝ))
  let Y : ℝ := 2 * (2 ^ (2 * d + 3) * S + 8 * 2 ^ d * S * (((f : ℝ) + 1) / (f : ℝ)))
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  refine ⟨X, Y, by dsimp only [X]; positivity, by dsimp only [Y]; positivity, ?_⟩
  intro x w w' ℓ h k hh hk hxw hxw' hkw hℓ c K
  let H : ℝ := (h : ℝ) + 1
  let T : ℝ := (k : ℝ) + 1
  have hH : 0 < H := by dsimp only [H]; positivity
  have hT : 0 < T := by dsimp only [T]; positivity
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by dsimp only [e]; omega)
  have hf : (f : ℝ) ≠ 0 := by exact_mod_cast (show f ≠ 0 by dsimp only [f]; omega)
  have hraw := box_pair_branch_sum hd x w w' ℓ hh hk hxw hxw' hkw hℓ c K
  refine hraw.trans_eq ?_
  change
    (2 ^ (2 * d + 3) * S * (H ^ 3 / H ^ (2 * d)) +
      8 * S * (((e : ℝ) + 1) / ((e : ℝ) * ((h + 1 : ℕ) : ℝ) ^ e))) +
    ((2 ^ (2 * d + 3) / (H ^ d * T ^ d) * (S * T ^ 3) +
      (8 * 2 ^ d / H ^ d) * (S * (((f : ℝ) + 1) / ((f : ℝ) * T ^ f)))) +
     (2 ^ (2 * d + 3) / (H ^ d * T ^ d) * (S * T ^ 3) +
      (8 * 2 ^ d / H ^ d) * (S * (((f : ℝ) + 1) / ((f : ℝ) * T ^ f))))) =
    X / H ^ e + Y / (H ^ d * T ^ f)
  rw [show ((h + 1 : ℕ) : ℝ) = H by simp [H]]
  have hpH : H ^ (2 * d) = H ^ 3 * H ^ e := by
    rw [← pow_add, show 3 + e = 2 * d by dsimp only [e]; omega]
  have hpT : T ^ d = T ^ 3 * T ^ f := by
    rw [← pow_add, show 3 + f = d by dsimp only [f]; omega]
  rw [hpH, hpT]
  dsimp only [X, Y]
  field_simp [hH.ne', hT.ne', he, hf] <;> ring

/-- A single coordinate plane projects injectively into the transverse
lattice. A nonnegative decreasing radial kernel can only grow under the projection. -/
theorem plane_radial_sum_le_projection {k : ℕ} (F : Finset (Vertex (k + 1)))
    (i : Fin (k + 1)) (w : Vertex (k + 1)) (R : ℕ)
    (hface : ∀ y ∈ F, y i = w i) (hrad : ∀ y ∈ F, linfDist w y ≤ R)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (hmono : Antitone f) :
    ∑ y ∈ F, f (linfDist w y) ≤
      ∑ z ∈ linfBall (Fin.removeNth i w) (R : ℤ), f (linfDist (Fin.removeNth i w) z) := by
  have hdrop (y : Vertex (k + 1)) :
      linfDist (Fin.removeNth i w) (Fin.removeNth i y) ≤ linfDist w y := by
    simpa using linfDist_removeNth_le w i (y i) (Fin.removeNth i y)
  have hinj (y z : Vertex (k + 1)) (hy : y ∈ F) (hz : z ∈ F)
      (he : Fin.removeNth i y = Fin.removeNth i z) : y = z := by
    have htop : y i = z i := (hface y hy).trans (hface z hz).symm
    calc
      y = Fin.insertNth (α := fun _ => ℤ) i (y i) (Fin.removeNth i y) := by simp
      _ = Fin.insertNth (α := fun _ => ℤ) i (z i) (Fin.removeNth i z) := by rw [htop, he]
      _ = z := by simp
  have hsubset : F.image (Fin.removeNth i) ⊆ linfBall (Fin.removeNth i w) (R : ℤ) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_linfBall_iff_dist _ _ (Int.natCast_nonneg R)).mpr
    simpa only [Int.toNat_natCast] using (hdrop y).trans (hrad y hy)
  calc
    _ ≤ ∑ y ∈ F, f (linfDist (Fin.removeNth i w) (Fin.removeNth i y)) :=
      Finset.sum_le_sum fun y _ => hmono (hdrop y)
    _ = ∑ z ∈ F.image (Fin.removeNth i), f (linfDist (Fin.removeNth i w) z) := by
      rw [Finset.sum_image (show Set.InjOn (Fin.removeNth i) (↑F : Set (Vertex (k + 1))) from
        fun _ hy _ hz he => hinj _ _ hy hz he)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z _ _ => hf _)

/-- The two radial face sums that occur after the boundary tripod estimate.
The first is cubic in the face radius. The second has cutoff decay. -/
theorem plane_boundary_error_radial_bounds {k : ℕ} (hk : 6 ≤ k) :
    ∃ D₀ D₁ : ℝ, 0 ≤ D₀ ∧ 0 ≤ D₁ ∧ ∀ (F : Finset (Vertex (k + 1)))
      (i : Fin (k + 1)) (w : Vertex (k + 1)) (R r : ℕ), 1 ≤ r →
      (∀ y ∈ F, y i = w i) → (∀ y ∈ F, linfDist w y ≤ R) →
      let K (y : Vertex (k + 1)) := (max (r : ℝ) (latticeDistance w y)) ^
        ((4 : ℝ) - ((k + 1 : ℕ) : ℝ))
      (∑ y ∈ F, K y) ≤ D₀ * ((R : ℝ) + 1) ^ 3 ∧
        (∑ y ∈ F, K y / ((linfDist w y + 1 : ℕ) : ℝ) ^ (k - 2)) ≤
          D₁ / (r : ℝ) ^ (k - 5) := by
  let B : ℝ := (2 : ℝ) ^ (k - 3)
  let C : ℝ := 2 * (k : ℝ) * 3 ^ (k - 1)
  let e := k - 5
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨B * C, B * C * (((e : ℝ) + 1) / (e : ℝ)), by positivity, by positivity, ?_⟩
  intro F i w R r hr hface hrad K
  let f (j : ℕ) : ℝ := 1 / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (k - 3)
  let g (j : ℕ) : ℝ := f j / ((j + 1 : ℕ) : ℝ) ^ (k - 2)
  have hf (j : ℕ) : 0 ≤ f j := by dsimp only [f]; positivity
  have hg (j : ℕ) : 0 ≤ g j := div_nonneg (hf j) (by positivity)
  have hfm : Antitone f := by
    intro a b hab
    dsimp only [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (max_le_max le_rfl (by exact_mod_cast Nat.succ_le_succ hab)) _
  have hgm : Antitone g := by
    intro a b hab
    exact (div_le_div_of_nonneg_right (hfm hab) (by positivity)).trans
      (div_le_div_of_nonneg_left (hf a) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hab) _))
  have hK (y : Vertex (k + 1)) : K y ≤ B * f (linfDist w y) := by
    have he : (4 : ℝ) - ((k + 1 : ℕ) : ℝ) = -((k - 3 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 3 ≤ k)]
      push_cast
      ring
    change (max (r : ℝ) (latticeDistance w y)) ^ ((4 : ℝ) - ((k + 1 : ℕ) : ℝ)) ≤ _
    rw [he, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_eq_one_div]
    simpa only [B, f, ← mul_div_assoc, mul_one] using literal_kernel_le hr w y (k - 3)
  let w' := Fin.removeNth i w
  have h₀ : ∑ z ∈ linfBall w' (R : ℤ), f (linfDist w' z) ≤ C * ((R : ℝ) + 1) ^ 3 :=
    ball_maxr_pow_cubic (by omega : 3 ≤ k) w' r R
  have h₁ : ∑ z ∈ linfBall w' (R : ℤ), g (linfDist w' z) ≤
      C * (((e : ℝ) + 1) / (e : ℝ)) / (r : ℝ) ^ e := by
    have h := radial_div_sum_le (by omega : 1 ≤ k) w' (k - 2) (by omega) (t := e)
      (by dsimp only [e]; omega) hr R
    rw [show (k - 1) - (k - 2) + (e + 1) = k - 3 by dsimp only [e]; omega] at h
    have hh : (∑ z ∈ linfBall w' (R : ℤ), g (linfDist w' z)) =
        ∑ z ∈ linfBall w' (R : ℤ),
          1 / (((linfDist w' z + 1 : ℕ) : ℝ) ^ (k - 2) *
            (max (r : ℝ) ((linfDist w' z + 1 : ℕ) : ℝ)) ^ (k - 3)) := by
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [g, f]
      rw [div_div, mul_comm]
    rw [hh]
    exact h.trans_eq (by dsimp only [C]; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  constructor
  · calc
      _ ≤ ∑ y ∈ F, B * f (linfDist w y) := Finset.sum_le_sum fun y _ => hK y
      _ = B * ∑ y ∈ F, f (linfDist w y) := by rw [Finset.mul_sum]
      _ ≤ B * (C * ((R : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left ((plane_radial_sum_le_projection F i w R hface hrad f hf hfm).trans h₀) hB
      _ = _ := by ring
  · calc
      _ ≤ ∑ y ∈ F, B * g (linfDist w y) := by
        apply Finset.sum_le_sum
        intro y _
        simpa only [g, mul_div_assoc] using
          div_le_div_of_nonneg_right (hK y) (by positivity :
            0 ≤ ((linfDist w y + 1 : ℕ) : ℝ) ^ (k - 2))
      _ = B * ∑ y ∈ F, g (linfDist w y) := by rw [Finset.mul_sum]
      _ ≤ B * (C * (((e : ℝ) + 1) / (e : ℝ)) / (r : ℝ) ^ e) :=
        mul_le_mul_of_nonneg_left ((plane_radial_sum_le_projection F i w R hface hrad g hg hgm).trans h₁) hB
      _ = _ := by dsimp only [e]; ring

/-- Actual Appendix A boundary error. The off-diagonal face sum is
estimated using the two radial bounds and the finite-domain tripod. -/
theorem appendix_wide_box_errBoundary_bound {k : ℕ} (hk : 6 ≤ k) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 2 ≤ m)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin (k + 1), SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin (k + 1)) (n r : ℕ) (x : Vertex (k + 1)),
      1 ≤ n → 1 ≤ r → 16 ≤ α / (m : ℝ) * (n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      let h := appendixWideHeight α m n
      let Q := appendixWideBox i h (m * h) x
      let F := appendixWideFace i h (m * h) x
      r ≤ h → appendixBoxClusterMean (criticalPoint (k + 1)) Q x (fun U => appendixBoxErrBoundary U F r) ≤
        K * (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ)) / (n : ℝ) := by
  let d := k + 1
  have hd : 7 ≤ d := by dsimp only [d]; omega
  obtain ⟨X, Y, hX, hY, hbranch⟩ := box_pair_branch_sum_scaled hd
  obtain ⟨D₀, D₁, hD₀, hD₁, hradial⟩ := plane_boundary_error_radial_bounds hk
  obtain ⟨U, V, hU, hV, htripod⟩ := appendix_slab_error_tripod (d := d) (by omega)
    C A B hC hA hB panis arm second
  let β := α / (m : ℝ)
  let Z : ℝ := 48 / β
  let L : ℝ := U ^ 3 * (X * D₀ * Z ^ 3 + Y * D₁)
  have hβ : 0 < β := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    dsimp only [β]
    positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨(2 * (m : ℝ) + 1) ^ (d - 1) * L * (16 / β), by positivity, ?_⟩
  intro i n r x hn hr hlarge hxi hx h Q F hrh
  let p := criticalPoint d
  let a : ℤ := -(n : ℤ)
  let b : ℤ := a + (h : ℤ)
  let ℓ := appendixSlabDepth i a b
  let H : ℝ := (h : ℝ) + 1
  let e := d - 6
  let f := d - 3
  let den : ℝ := (h : ℝ) ^ d * (r : ℝ) ^ e
  obtain ⟨hh, hhR, hR⟩ := appendixWideHeight_scales α hα0 m n hm hlarge
  obtain ⟨hxQ, hQT, hQheight, hFQ, hFheight, _⟩ :=
    appendixWideBox_geometry i x hα1 hhR hR hxi hx
  have hQcube : Q ⊆ (cube n : Finset (Vertex d)) := by
    rw [appendix_cube_eq_centeredBox]
    exact hQT
  have hQslab (u : Vertex d) (hu : u ∈ Q) : a ≤ u i ∧ u i ≤ b :=
    ⟨(mem_centeredBox.mp (hQT hu) i).1, hQheight u hu⟩
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hden : 0 < den := by dsimp only [den]; positivity
  have hhH : (h : ℝ) ≤ H := by dsimp only [H]; linarith
  have hrH : (r : ℝ) ≤ H := (show (r : ℝ) ≤ h by exact_mod_cast hrh).trans hhH
  have hdenH : den ≤ H ^ (2 * d - 6) := by
    rw [← show d + e = 2 * d - 6 by dsimp only [e]; omega, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hh0.le hhH _) (pow_le_pow_left₀ hr0.le hrH _)
      (by positivity) (by positivity)
  have hRadius : ((2 * n : ℕ) : ℝ) + 1 ≤ Z * H := by
    change 16 ≤ β * (n : ℝ) at hlarge
    have hf := Nat.lt_floor_add_one (β * (n : ℝ) / 8)
    change β * (n : ℝ) / 8 < (h : ℝ) + 1 at hf
    have hlo : β * (n : ℝ) / 16 ≤ h := by linarith
    have hn' : (n : ℝ) ≤ (16 / β) * (h : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ]
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    calc
      _ ≤ 3 * (n : ℝ) := by linarith
      _ ≤ 3 * ((16 / β) * (h : ℝ)) := mul_le_mul_of_nonneg_left hn' (by norm_num)
      _ = Z * (h : ℝ) := by dsimp only [Z]; ring
      _ ≤ Z * H := mul_le_mul_of_nonneg_left hhH hZ
  have hperW (w : Vertex d) (hw : w ∈ F) :
      (∑ v ∈ F.erase w, (percolation d p).real {ω |
        (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w ∧
        (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v}
          * (max (r : ℝ) (latticeDistance w v)) ^ ((4 : ℝ) - (d : ℝ))) ≤ L / den := by
    let F' := F.erase w
    let K (v : Vertex d) := (max (r : ℝ) (latticeDistance w v)) ^ ((4 : ℝ) - (d : ℝ))
    let s (v : Vertex d) : ℝ := (linfDist w v + 1 : ℕ)
    let P (v : Vertex d) := (percolation d p).real {ω |
      (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w ∧
      (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v}
    have hwQ := hFQ hw
    have hwb := hFheight w hw
    have hxw := appendixSlab_height_le_distance i a h x w hxi hwb
    obtain ⟨_, hbd⟩ := htripod Q i a b hQslab x hxQ hxi w hwQ hwb
    have hpair (v : Vertex d) (hv : v ∈ F') :
        P v ≤ U ^ 3 * (X / H ^ (2 * d - 3) + Y / (H ^ d * s v ^ f)) := by
      obtain ⟨hvne, hvF⟩ := Finset.mem_erase.mp hv
      have hvQ := hFQ hvF
      have hvb := hFheight v hvF
      have hxv := appendixSlab_height_le_distance i a h x v hxi hvb
      have hkdist : 1 ≤ linfDist w v := by
        by_contra hh
        have hdist : linfDist w v = 0 := by omega
        apply hvne
        funext j
        have hcoord : (w j - v j).natAbs ≤ linfDist w v :=
          Finset.le_sup (f := fun j => (w j - v j).natAbs) (Finset.mem_univ j)
        omega
      have hℓ (u : Vertex d) :
          ℓ u ≤ 1 + min (linfDist x u) (min (linfDist u w) (linfDist u v)) := by
        have h₁ := appendixSlabDepth_le_end_distance i a b x u (Or.inl hxi)
        have h₂ := appendixSlabDepth_le_end_distance i a b w u (Or.inr hwb)
        have h₃ := appendixSlabDepth_le_end_distance i a b v u (Or.inr hvb)
        rw [linfDist_comm w u] at h₂
        rw [linfDist_comm v u] at h₃
        exact (le_min h₁ (le_min h₂ h₃)).trans (by omega)
      have hbranch' := hbranch x w v ℓ h (linfDist w v) hh hkdist hxw hxv le_rfl hℓ 0 n
      let T (u : Vertex d) : ℝ := ((ℓ u + 1 : ℕ) : ℝ) ^ 3 /
        (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d *
          ((linfDist u v + 1 : ℕ) : ℝ) ^ d)
      have hsum : ∑ u ∈ Q, T u ≤ X / H ^ (2 * d - 3) + Y / (H ^ d * s v ^ f) := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg hQcube (fun u _ _ => by dsimp only [T]; positivity)).trans ?_
        simpa only [cube_eq_linfBall, H, s, f, T, Nat.cast_add, Nat.cast_one] using hbranch'
      dsimp only [P]
      rw [appendix_joint_reachable_eq_connection hxQ hwQ hvQ]
      refine (hbd v hvQ hvb).trans ?_
      refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [T, ℓ]
      rw [linfDist_comm w u, linfDist_comm v u]
      push_cast
      ring
    have hface (v : Vertex d) (hv : v ∈ F') : v i = w i :=
      (hFheight v (Finset.mem_erase.mp hv).2).trans hwb.symm
    have hrad (v : Vertex d) (hv : v ∈ F') : linfDist w v ≤ 2 * n := by
      have h := (mem_linfBall_iff_dist w v (Int.natCast_nonneg (2 * n))).mp
        (cube_subset_linfBall_two (hQcube hwQ) (hQcube (hFQ (Finset.mem_erase.mp hv).2)))
      simpa only [Int.toNat_natCast] using h
    obtain ⟨h₀, h₁⟩ := hradial F' i w (2 * n) r hr hface hrad
    have h₀' : (∑ v ∈ F', K v) ≤ D₀ * (Z * H) ^ 3 :=
      h₀.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRadius _) hD₀)
    have h₁' : (∑ v ∈ F', K v / s v ^ f) ≤ D₁ / (r : ℝ) ^ e := by
      simpa only [f, e, d, show k + 1 - 3 = k - 2 by omega, show k + 1 - 6 = k - 5 by omega] using h₁
    have hx0 : 0 ≤ X / H ^ (2 * d - 3) := by positivity
    have hy0 : 0 ≤ Y / H ^ d := by positivity
    have hyH : Y / H ^ d ≤ Y / (h : ℝ) ^ d :=
      div_le_div_of_nonneg_left hY (pow_pos hh0 _) (pow_le_pow_left₀ hh0.le hhH _)
    have hinner : X / H ^ (2 * d - 3) * (D₀ * (Z * H) ^ 3) +
        Y / H ^ d * (D₁ / (r : ℝ) ^ e) ≤ (X * D₀ * Z ^ 3 + Y * D₁) / den := by
      calc
        _ ≤ X / H ^ (2 * d - 3) * (D₀ * (Z * H) ^ 3) +
            Y / (h : ℝ) ^ d * (D₁ / (r : ℝ) ^ e) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hyH (by positivity))
        _ = X * D₀ * Z ^ 3 / H ^ (2 * d - 6) + Y * D₁ / den := by
          rw [show H ^ (2 * d - 3) = H ^ 3 * H ^ (2 * d - 6) by
            rw [← pow_add, show 3 + (2 * d - 6) = 2 * d - 3 by omega]]
          dsimp only [den]
          field_simp [hH.ne', hh0.ne', hr0.ne'] <;> ring
        _ ≤ X * D₀ * Z ^ 3 / den + Y * D₁ / den :=
          add_le_add (div_le_div_of_nonneg_left (by positivity) hden hdenH) le_rfl
        _ = _ := by rw [add_div]
    change (∑ v ∈ F', P v * K v) ≤ L / den
    calc
      _ ≤ ∑ v ∈ F', (U ^ 3 * (X / H ^ (2 * d - 3) + Y / (H ^ d * s v ^ f))) * K v :=
        Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right (hpair v hv) (by dsimp only [K]; positivity)
      _ = U ^ 3 * (X / H ^ (2 * d - 3) * (∑ v ∈ F', K v) +
          Y / H ^ d * (∑ v ∈ F', K v / s v ^ f)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ U ^ 3 * (X / H ^ (2 * d - 3) * (D₀ * (Z * H) ^ 3) +
          Y / H ^ d * (D₁ / (r : ℝ) ^ e)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h₀' hx0)
          (mul_le_mul_of_nonneg_left h₁' hy0)) (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_left hinner (by positivity)).trans_eq (by dsimp only [L]; ring)
  exact (appendixBoxClusterMean_errBoundary_bound p Q F x hxQ r hFQ (L / den) hperW).trans
    (appendixWideFace_error_scale hd hα0 m hm i n r x hn hr hlarge L hL)

end NearCritical
