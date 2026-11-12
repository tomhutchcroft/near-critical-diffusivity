module

public import NearCritical.AppendixErrBoundary
public import NearCritical.AppendixBoxWideLower
public import NearCritical.AppendixSlabErrorTripods

/-! The uniform Appendix A cluster error on the actual wide prism. -/
@[expose] public section
noncomputable section
namespace NearCritical
open AppendixVariance MeasureTheory Section8
open scoped Classical

/-- The two regions of the existing cluster convolution estimate have a
common uniform scale when the cutoff is at most the exploration height. -/
theorem perW_bound_scaled {d : ℕ} (hd : 7 ≤ d) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ (x w : Vertex d) (ℓ : Vertex d → ℕ) (r h : ℕ),
      1 ≤ r → r ≤ h → 1 ≤ h → h ≤ linfDist x w →
      (∀ u, ℓ u ≤ 1 + min (linfDist x u) (linfDist u w)) →
      ∀ (c : Vertex d) (K : ℕ) (P A : Vertex d → ℝ), (∀ u, 0 ≤ A u) →
      (∀ u, A u ≤ ((ℓ u + 1 : ℕ) : ℝ) ^ 3 /
        (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d)) →
      (∀ v ∈ linfBall c (K : ℤ),
        P v ≤ ∑ u ∈ linfBall c (K : ℤ), A u * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1))) →
      (∑ v ∈ linfBall c (K : ℤ),
        P v * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))) ≤
        J / ((h : ℝ) ^ d * (r : ℝ) ^ (d - 6)) := by
  let e := d - 6
  let f := 2 * d - 6
  let S : ℝ := 2 * (d : ℝ) * 3 ^ (d - 1)
  let V : ℝ := 2 ^ (2 * d) * S +
    (2 ^ (d - 2) * S + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1))))
  let C₁ : ℝ := 8 * 2 ^ d * S * (((e : ℝ) + 1) / (e : ℝ))
  let C₂ : ℝ := 2 ^ (2 * d) * S
  let C₃ : ℝ := 8 * S * (((f : ℝ) + 1) / (f : ℝ))
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have h₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have h₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  have h₃ : 0 ≤ C₃ := by dsimp only [C₃]; positivity
  refine ⟨V * (C₁ + C₂ + C₃), by positivity, ?_⟩
  intro x w ℓ r h hr hrh hh hxw hℓ c K P A hA hApt hBK
  let H : ℝ := (h : ℝ) + 1
  let R : ℝ := r
  let D : ℝ := (h : ℝ) ^ d * R ^ e
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hr0 : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < r by omega)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hhH : (h : ℝ) ≤ H := by dsimp only [H]; linarith
  have hrH : R ≤ H := (show (r : ℝ) ≤ h by exact_mod_cast hrh).trans hhH
  have hd₁ : D ≤ H ^ d * R ^ e :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh0.le hhH _) (by positivity)
  have hd₂ : D ≤ H ^ f := by
    have he : d + e = f := by dsimp only [e, f]; omega
    rw [← he, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hh0.le hhH _) (pow_le_pow_left₀ hr0.le hrH _)
      (by positivity) (by positivity)
  have hcancel : H ^ 3 / H ^ (2 * d - 3) = 1 / H ^ f := by
    have he : 2 * d - 3 = 3 + f := by dsimp only [f]; omega
    rw [he, pow_add, ← div_div, div_self (pow_ne_zero _ hH.ne')]
  have hraw :
      (∑ v ∈ linfBall c (K : ℤ),
        P v * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))) ≤
        V * ((8 * 2 ^ d / H ^ d) * (S * (((e : ℝ) + 1) / ((e : ℝ) * R ^ e)))) +
          V * (C₂ * (H ^ 3 / H ^ (2 * d - 3)) +
            8 * S * (((f : ℝ) + 1) / ((f : ℝ) * H ^ f))) := by
    simpa only [Nat.cast_add, Nat.cast_one, H, R, V, S, C₂, e, f] using
      (perW_bound hd x w ℓ hr hh hxw hℓ c K P A hA hApt hBK)
  refine hraw.trans ?_
  calc
    _ = V * (C₁ / (H ^ d * R ^ e) + (C₂ + C₃) / H ^ f) := by
      rw [hcancel]
      dsimp only [C₁, C₃]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ V * (C₁ / D + (C₂ + C₃) / D) :=
      mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_left h₁ hD hd₁)
        (div_le_div_of_nonneg_left (add_nonneg h₂ h₃) hD hd₂)) hV
    _ = _ := by dsimp only [D, R, e]; ring

/-- Multiplying a per-point error by the wide face cardinality leaves the
required inverse cube radius. The coefficient is independent of the cutoff. -/
theorem appendixWideFace_error_scale {d : ℕ} (hd : 7 ≤ d) {α : ℝ} (hα0 : 0 < α)
    (m : ℕ) (hm : 2 ≤ m) (i : Fin d) (n r : ℕ) (x : Vertex d)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hlarge : 16 ≤ α / (m : ℝ) * (n : ℝ))
    (L : ℝ) (hL : 0 ≤ L) :
    let h := appendixWideHeight α m n
    let F := appendixWideFace i h (m * h) x
    (F.card : ℝ) * (L / ((h : ℝ) ^ d * (r : ℝ) ^ (d - 6))) ≤
      ((2 * (m : ℝ) + 1) ^ (d - 1) * L * (16 / (α / (m : ℝ)))) *
        (r : ℝ) ^ ((6 : ℝ) - (d : ℝ)) / (n : ℝ) := by
  intro h F
  let β := α / (m : ℝ)
  let M : ℝ := (2 * (m : ℝ) + 1) ^ (d - 1)
  let den : ℝ := (h : ℝ) ^ d * (r : ℝ) ^ (d - 6)
  have hβ : 0 < β := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    dsimp only [β]
    positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hh := (appendixWideHeight_scales α hα0 m n hm hlarge).1
  have hwidth : 2 * (m * h) + 1 ≤ (2 * m + 1) * h := by
    rw [Nat.add_mul, one_mul, Nat.mul_assoc]
    omega
  have hcardN : F.card ≤ ((2 * m + 1) * h) ^ (d - 1) :=
    (appendixWideFace_card_le i h (m * h) x).trans (Nat.pow_le_pow_left hwidth _)
  have hcard : (F.card : ℝ) ≤ M * (h : ℝ) ^ (d - 1) := by
    have ht : (F.card : ℝ) ≤ ((2 * (m : ℝ) + 1) * (h : ℝ)) ^ (d - 1) := by
      exact_mod_cast hcardN
    rwa [mul_pow] at ht
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change 16 ≤ β * (n : ℝ) at hlarge
  have hlo : β * (n : ℝ) / 16 ≤ (h : ℝ) := by
    have ht := Nat.lt_floor_add_one (β * (n : ℝ) / 8)
    change β * (n : ℝ) / 8 < (h : ℝ) + 1 at ht
    linarith
  have hre : (6 : ℝ) - (d : ℝ) = -((d - 6 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 6 ≤ d)]
    push_cast
    ring
  calc
    _ ≤ (M * (h : ℝ) ^ (d - 1)) * (L / den) :=
      mul_le_mul_of_nonneg_right hcard (by dsimp only [den]; positivity)
    _ = M * L / ((h : ℝ) * (r : ℝ) ^ (d - 6)) := by
      dsimp only [den]
      rw [show (h : ℝ) ^ d = (h : ℝ) ^ (d - 1) * (h : ℝ) by
        rw [← pow_succ, show d - 1 + 1 = d by omega]]
      field_simp [hh0.ne', hr0.ne'] <;> ring
    _ ≤ M * L / ((β * (n : ℝ) / 16) * (r : ℝ) ^ (d - 6)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hlo (by positivity))
    _ = _ := by
      change _ = M * L * (16 / β) * (r : ℝ) ^ ((6 : ℝ) - (d : ℝ)) / (n : ℝ)
      rw [hre, Real.rpow_neg hr0.le, Real.rpow_natCast]
      field_simp [hβ.ne', hn0.ne', hr0.ne'] <;> ring

/-- Joint reachability and the pair of restricted connection events agree
when the three endpoints belong to the finite domain. -/
theorem appendix_joint_reachable_eq_connection {d : ℕ} {Q : Finset (Vertex d)}
    {x w v : Vertex d} (hx : x ∈ Q) (hw : w ∈ Q) (hv : v ∈ Q) :
    {ω | (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w ∧
      (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v} =
      connectionToSetEvent (Q : Set (Vertex d)) x {w} ∩
        connectionToSetEvent (Q : Set (Vertex d)) x {v} := by
  ext ω
  constructor
  · intro hω
    exact ⟨⟨hx, w, rfl, hw, hω.1⟩, ⟨hx, v, rfl, hv, hω.2⟩⟩
  · rintro ⟨⟨_, w', hw', _, h₁⟩, ⟨_, v', hv', _, h₂⟩⟩
    obtain rfl : w' = w := hw'
    obtain rfl : v' = v := hv'
    exact ⟨h₁, h₂⟩

/-- Actual Appendix A cluster error on the wide prism. The coefficient is
uniform in the enclosing cube scale, root, face, and cutoff. -/
theorem appendix_wide_box_errCluster_bound {d : ℕ} (hd : 7 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 2 ≤ m)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n r : ℕ) (x : Vertex d),
      1 ≤ n → 1 ≤ r → 16 ≤ α / (m : ℝ) * (n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      let h := appendixWideHeight α m n
      let Q := appendixWideBox i h (m * h) x
      let F := appendixWideFace i h (m * h) x
      r ≤ h → appendixBoxClusterMean (criticalPoint d) Q x (fun U => appendixBoxErrCluster U F r) ≤
        K * (r : ℝ) ^ ((6 : ℝ) - (d : ℝ)) / (n : ℝ) := by
  obtain ⟨J, hJ, hconv⟩ := perW_bound_scaled hd
  obtain ⟨U, V, hU, hV, htripod⟩ := appendix_slab_error_tripod (by omega : 1 ≤ d)
    C A B hC hA hB panis arm second
  let W : ℝ := U ^ 2 * V
  let L : ℝ := W * (2 : ℝ) ^ (d - 2) * J
  let M : ℝ := (2 * (m : ℝ) + 1) ^ (d - 1)
  let β := α / (m : ℝ)
  have hβ : 0 < β := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    dsimp only [β]
    positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨M * L * (16 / β), by positivity, ?_⟩
  intro i n r x hn hr hlarge hxi hx h Q F hrh
  let p := criticalPoint d
  let a : ℤ := -(n : ℤ)
  let b : ℤ := a + (h : ℤ)
  let ℓ := appendixSlabDepth i a b
  let den : ℝ := (h : ℝ) ^ d * (r : ℝ) ^ (d - 6)
  obtain ⟨hh, hhR, hR⟩ := appendixWideHeight_scales α hα0 m n hm hlarge
  obtain ⟨hxQ, hQT, hQheight, hFQ, hFheight, _⟩ :=
    appendixWideBox_geometry i x hα1 hhR hR hxi hx
  have hQcube : Q ⊆ (cube n : Finset (Vertex d)) := by
    rw [appendix_cube_eq_centeredBox]
    exact hQT
  have hQslab (u : Vertex d) (hu : u ∈ Q) : a ≤ u i ∧ u i ≤ b :=
    ⟨(mem_centeredBox.mp (hQT hu) i).1, hQheight u hu⟩
  have hperW (w : Vertex d) (hw : w ∈ F) :
      (∑ v ∈ Q, (percolation d p).real {ω |
        (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w ∧
        (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v}
          * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))) ≤ L / den := by
    have hwQ := hFQ hw
    have hwb := hFheight w hw
    have hxw : h ≤ linfDist x w := appendixSlab_height_le_distance i a h x w hxi hwb
    have hℓ (u : Vertex d) : ℓ u ≤ 1 + min (linfDist x u) (linfDist u w) := by
      have hl := appendixSlabDepth_le_end_distance i a b x u (Or.inl hxi)
      have hr := appendixSlabDepth_le_end_distance i a b w u (Or.inr hwb)
      rw [linfDist_comm w u] at hr
      exact (le_min hl hr).trans (by omega)
    let B₀ (u : Vertex d) : ℝ := ((ℓ u + 1 : ℕ) : ℝ) ^ 3 /
      (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d)
    let A₀ (u : Vertex d) : ℝ := if u ∈ Q then B₀ u else 0
    let P (v : Vertex d) : ℝ :=
      ∑ u ∈ (cube n : Finset (Vertex d)), A₀ u * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1))
    have hB₀ (u : Vertex d) : 0 ≤ B₀ u := by dsimp only [B₀]; positivity
    have hA₀ (u : Vertex d) : 0 ≤ A₀ u := by
      by_cases hu : u ∈ Q <;> simp [A₀, hu, hB₀ u]
    have hA₁ (u : Vertex d) : A₀ u ≤ B₀ u := by
      by_cases hu : u ∈ Q <;> simp [A₀, hu, hB₀ u]
    have hP (v : Vertex d) : 0 ≤ P v :=
      Finset.sum_nonneg fun u _ => mul_nonneg (hA₀ u) (by positivity)
    have hP_eq (v : Vertex d) :
        P v = ∑ u ∈ Q, B₀ u * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) := by
      unfold P
      rw [← Finset.sum_subset hQcube (fun u _ hu => by simp [A₀, hu])]
      exact Finset.sum_congr rfl fun u hu => by simp [A₀, hu]
    have hrk := hconv x w ℓ r h hr hrh hh hxw hℓ 0 n P A₀ hA₀ hA₁ (fun _ _ => le_rfl)
    have hraw := sum_real_kernel_le_of_reg (by omega : 2 ≤ d) hr w 0 n P hP _ hrk
    obtain ⟨hcl, _⟩ := htripod Q i a b hQslab x hxQ hxi w hwQ hwb
    have hjoint (v : Vertex d) (hv : v ∈ Q) :
        (percolation d p).real {ω |
          (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w ∧
          (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v} ≤ W * P v := by
      rw [appendix_joint_reachable_eq_connection hxQ hwQ hv, hP_eq]
      refine (hcl v hv).trans_eq ?_
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [B₀, ℓ]
      rw [linfDist_comm v u]
      push_cast
      ring
    let k (v : Vertex d) := (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))
    calc
      _ ≤ ∑ v ∈ Q, (W * P v) * k v :=
        Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right (hjoint v hv) (by dsimp only [k]; positivity)
      _ = W * ∑ v ∈ Q, P v * k v := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
      _ ≤ W * ∑ v ∈ (cube n : Finset (Vertex d)), P v * k v :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hQcube
          (fun v _ _ => mul_nonneg (hP v) (by dsimp only [k]; positivity))) hW
      _ ≤ W * ((2 : ℝ) ^ (d - 2) * (J / den)) := mul_le_mul_of_nonneg_left hraw hW
      _ = _ := by dsimp only [L]; ring
  have hagg := appendixBoxClusterMean_errCluster_bound p Q F x hxQ r hFQ (L / den) hperW
  exact hagg.trans (appendixWideFace_error_scale hd hα0 m hm i n r x hn hr hlarge L hL)

end NearCritical
