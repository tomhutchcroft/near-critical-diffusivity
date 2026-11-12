module

public import NearCritical.SplitCrossDirectCountMoment
public import NearCritical.Section8Convolution
public import NearCritical.Section10FaceCountUpper
public import Mathlib.Analysis.MeanInequalities

/-! Masses and mixed moments (item B of the direct proof of `SplitCrossInput`,
quantitative form).

* `integral_prod_le_scaled`: scaled AM--GM replacing Hölder: for `n` nonnegative
  random variables and scales `s_j > 0`,
  `E[∏ X_j] ≤ (∏ s_j) · n⁻¹ · Σ_j E[(X_j / s_j)^n]`.
* `box_branch_mass_le`: from the sup-norm Green upper bound
  (`CriticalSupGreenUpper`, a consequence of (A)), for every `u`,
  `Σ_{w ∈ Λ_N} P[u ↔ w in Λ_N] ≤ G (1 + K (2N+1)^2)`.
* `box_interior_count_moment_le`: `E[#{v ∈ Y : u ↔ v in Λ_N}^n] ≤ γ(n,n) M^(2n-1)`
  for `Y ⊆ Λ_N`, with `M = G (1 + K (2N+1)^2)` (order `N^2`).
* `box_face_count_moment_le`: `E[#{y ∈ face : u ↔ y in Λ_N}^n] ≤ γ(n,n) B^n M^(n-1)`
  with `B` the box-face first moment (`BoxFaceFirstMoment`, already derived
  from the cited pioneer bound).
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory
open scoped Classical BigOperators

variable {d : ℕ}

/-- Pointwise scaled AM--GM. -/
theorem prod_le_scaled_sum_pow {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hs : ∀ j, 0 < s j)
    (hx : ∀ j, 0 ≤ x j) :
    ∏ j, x j ≤ (∏ j, s j) * ((n : ℝ)⁻¹ * ∑ j, (x j / s j) ^ n) := by
  have hz : ∀ j, 0 ≤ x j / s j := fun j => div_nonneg (hx j) (hs j).le
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw : ∑ _j : Fin n, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin n => (n : ℝ)⁻¹)
    (fun j => (x j / s j) ^ n) (fun _ _ => by positivity) hw (fun j _ => pow_nonneg (hz j) n)
  have hroot : ∀ j : Fin n, ((x j / s j) ^ n) ^ ((n : ℝ)⁻¹) = x j / s j :=
    fun j => Real.pow_rpow_inv_natCast (hz j) hn.ne'
  simp only [hroot] at hgm
  rw [← Finset.mul_sum] at hgm
  have hsplit : ∏ j, x j = (∏ j, s j) * ∏ j, (x j / s j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by
      have := (hs j).ne'
      field_simp)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hgm (Finset.prod_nonneg (fun j _ => (hs j).le))

/-- **Scaled AM--GM for expectations** (used in place of Hölder). -/
theorem integral_prod_le_scaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (hn : 0 < n) (X : Fin n → Ω → ℝ) (s : Fin n → ℝ) (hs : ∀ j, 0 < s j)
    (hX : ∀ j ω, 0 ≤ X j ω) (hprod : Integrable (fun ω => ∏ j, X j ω) μ)
    (hpow : ∀ j, Integrable (fun ω => (X j ω / s j) ^ n) μ) :
    ∫ ω, ∏ j, X j ω ∂μ ≤ (∏ j, s j) * ((n : ℝ)⁻¹ * ∑ j, ∫ ω, (X j ω / s j) ^ n ∂μ) := by
  have hpt : ∀ ω, ∏ j, X j ω ≤ (∏ j, s j) * ((n : ℝ)⁻¹ * ∑ j, (X j ω / s j) ^ n) :=
    fun ω => prod_le_scaled_sum_pow hn (fun j => X j ω) s hs (fun j => hX j ω)
  have hint : Integrable (fun ω => (∏ j, s j) * ((n : ℝ)⁻¹ * ∑ j, (X j ω / s j) ^ n)) μ :=
    ((integrable_finset_sum _ (fun j _ => hpow j)).const_mul _).const_mul _
  calc ∫ ω, ∏ j, X j ω ∂μ ≤ ∫ ω, (∏ j, s j) * ((n : ℝ)⁻¹ * ∑ j, (X j ω / s j) ^ n) ∂μ :=
        integral_mono hprod hint hpt
    _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_finset_sum _ (fun j _ => hpow j)]

lemma latticeDistance_le_of_mem_centeredBox {N : ℕ} {u w : Vertex d}
    (hu : u ∈ centeredBox d N) (hw : w ∈ centeredBox d N) :
    latticeDistance u w ≤ ((2 * N : ℕ) : ℝ) := by
  unfold latticeDistance
  refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
  have h1 := mem_centeredBox.mp hu i
  have h2 := mem_centeredBox.mp hw i
  show dist ((u i : ℤ) : ℝ) ((w i : ℤ) : ℝ) ≤ _
  rw [Real.dist_eq, abs_le]
  have a1 : (-(N : ℤ) : ℝ) ≤ ((u i : ℤ) : ℝ) := by exact_mod_cast h1.1
  have a2 : ((u i : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by exact_mod_cast h1.2
  have b1 : (-(N : ℤ) : ℝ) ≤ ((w i : ℤ) : ℝ) := by exact_mod_cast h2.1
  have b2 : ((w i : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by exact_mod_cast h2.2
  push_cast at a1 a2 b1 b2 ⊢
  constructor <;> linarith

/-- The mass constant of the box of radius `N`. -/
def boxMass (d : ℕ) (G : ℝ) (N : ℕ) : ℝ :=
  G * (1 + (2 * (d : ℝ) * 3 ^ (d - 1)) * (((2 * N : ℕ) : ℝ) + 1) ^ 2)

lemma boxMass_nonneg {G : ℝ} (hG : 0 ≤ G) (N : ℕ) : 0 ≤ boxMass d G N := by
  unfold boxMass
  positivity

/-- Sum of restricted two-point functions over any subset of the box. -/
theorem box_mass_le (hd : 2 ≤ d) {G : ℝ} (hG0 : 0 ≤ G) (hG : CriticalSupGreenUpper d G) (N : ℕ)
    {Y : Finset (Vertex d)} (hY : Y ⊆ centeredBox d N) (u : Vertex d) :
    ∑ v ∈ Y, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d N : Set (Vertex d)) u {v}) ≤ boxMass d G N := by
  by_cases hu : u ∈ centeredBox d N
  · have h1 : ∀ v ∈ Y, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (centeredBox d N : Set (Vertex d)) u {v}) ≤
        G * (max 1 (latticeDistance u v)) ^ ((2 : ℝ) - (d : ℝ)) := fun v _ =>
      (measureReal_mono (connectionToSetEvent_singleton_subset _ u v)
        (measure_ne_top _ _)).trans (hG u v)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    unfold boxMass
    exact mul_le_mul_of_nonneg_left
      (Section8.sum_green_ball_le hd (2 * N) Y u
        (fun x hx => latticeDistance_le_of_mem_centeredBox hu (hY hx))) hG0
  · have h0 : ∀ v ∈ Y, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (centeredBox d N : Set (Vertex d)) u {v}) = 0 := by
      intro v _
      have hempty : connectionToSetEvent (centeredBox d N : Set (Vertex d)) u {v} = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx, _⟩
        exact hu (Finset.mem_coe.mp hx)
      rw [hempty, measureReal_empty]
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    exact boxMass_nonneg hG0 N

/-- **Interior count moments**: order `N^(4n-2)`. -/
theorem box_interior_count_moment_le (hd : 2 ≤ d) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : CriticalSupGreenUpper d G) (N n : ℕ) (hn : 0 < n) {Y : Finset (Vertex d)}
    (hY : Y ⊆ centeredBox d N) (hYne : 0 < Y.card) {u : Vertex d} (hu : u ∈ centeredBox d N) :
    ∫ ω, countIn (centeredBox d N : Set (Vertex d)) Y u ω ^ n
        ∂percolation d (criticalPoint d) ≤
      (gammaN n n : ℝ) * boxMass d G N ^ n * boxMass d G N ^ (n - 1) :=
  countIn_moment_le n hn (criticalPoint d) (centeredBox d N) Y hYne
    (boxMass_nonneg hG0 N) (boxMass_nonneg hG0 N)
    (fun u' => box_mass_le hd hG0 hG N hY u')
    (fun u' => box_mass_le hd hG0 hG N (Finset.Subset.refl _) u') hu

/-- **Face count moments**: order `N^(2n-2)`. -/
theorem box_face_count_moment_le (hd : 2 ≤ d) {G B : ℝ} (hG0 : 0 ≤ G) (hB0 : 0 ≤ B)
    (hG : CriticalSupGreenUpper d G) (hBm : Section10.BoxFaceFirstMoment d B) (N n : ℕ)
    (hn : 0 < n) (f : Fin d × Bool) (hface : 0 < (signedCubeFace d N f).card)
    {u : Vertex d} (hu : u ∈ centeredBox d N) :
    ∫ ω, countIn (centeredBox d N : Set (Vertex d)) (signedCubeFace d N f) u ω ^ n
        ∂percolation d (criticalPoint d) ≤
      (gammaN n n : ℝ) * B ^ n * boxMass d G N ^ (n - 1) := by
  refine countIn_moment_le n hn (criticalPoint d) (centeredBox d N) (signedCubeFace d N f) hface
    hB0 (boxMass_nonneg hG0 N) (fun u' => ?_)
    (fun u' => box_mass_le hd hG0 hG N (Finset.Subset.refl _) u') hu
  by_cases hu' : u' ∈ centeredBox d N
  · exact hBm N u' hu' f
  · have h0 : ∀ v ∈ signedCubeFace d N f, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (centeredBox d N : Set (Vertex d)) u' {v}) = 0 := by
      intro v _
      have hempty : connectionToSetEvent (centeredBox d N : Set (Vertex d)) u' {v} = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx, _⟩
        exact hu' (Finset.mem_coe.mp hx)
      rw [hempty, measureReal_empty]
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    exact hB0

end NearCritical.SplitCrossDirect
end
