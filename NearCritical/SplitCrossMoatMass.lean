module

public import NearCritical.SplitCrossOutwardGeometry
public import NearCritical.AppendixBoxFaceBudget
public import NearCritical.AppendixBoundaryTopFace

/-! The Green mass of a branch's own moat seen from an outward point.
An inverse-square bound is enough for the smallness estimate, and its
one-dimensional tail has an elementary finite telescoping bound. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open scoped Classical

def moatGreen {d : ℕ} (x y : Vertex d) : ℝ :=
  (max 1 (latticeDistance x y)) ^ ((2 : ℝ) - (d : ℝ))

theorem moatGreen_nonneg {d : ℕ} (x y : Vertex d) : 0 ≤ moatGreen x y :=
  Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

theorem moatGreen_le_invSq {d : ℕ} (hd : 4 ≤ d) {s : ℝ} (hs : 1 ≤ s)
    {x y : Vertex d} (h : s ≤ latticeDistance x y) :
    moatGreen x y ≤ 1 / s ^ 2 := by
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hs' : 0 < s := zero_lt_one.trans_le hs
  unfold moatGreen
  calc
    _ ≤ s ^ ((2 : ℝ) - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hs' (h.trans (le_max_right _ _)) (by linarith)
    _ ≤ s ^ (-((2 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hs (by norm_num; linarith)
    _ = 1 / s ^ 2 := by rw [Real.rpow_neg hs'.le, Real.rpow_natCast, inv_eq_one_div]

private theorem invSq_step (u : ℝ) (hu : 0 < u) :
    1 / (u + 1)^2 ≤ 1 / u - 1 / (u + 1) := by
  calc
    _ ≤ 1 / (u * (u + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = _ := by
      field_simp [ne_of_gt hu]
      <;> ring

private theorem finite_invSq_tail (N ρ : ℕ) (hρ : 0 < ρ) :
    (∑ k ∈ Finset.range N, 1 / ((ρ : ℝ) + ((N - k : ℕ) : ℝ))^2) ≤
      1 / (ρ : ℝ) - 1 / ((ρ : ℝ) + (N : ℝ)) := by
  induction N generalizing ρ with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have heq : (∑ k ∈ Finset.range N, 1 / ((ρ : ℝ) + ((N + 1 - k : ℕ) : ℝ))^2) =
        ∑ k ∈ Finset.range N, 1 / ((((ρ + 1 : ℕ) : ℝ)) + ((N - k : ℕ) : ℝ))^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hdiff : N + 1 - k = (N - k) + 1 := by have := Finset.mem_range.mp hk; omega
      rw [hdiff]
      push_cast
      ring
    rw [heq]
    have hi := ih (ρ + 1) (by omega)
    have hs := invSq_step (ρ : ℝ) (by exact_mod_cast hρ)
    have hOne : N + 1 - N = 1 := by omega
    rw [hOne]
    push_cast at hi ⊢
    rw [show (ρ : ℝ) + ((N : ℝ) + 1) = (ρ : ℝ) + 1 + (N : ℝ) by ring]
    linarith

private theorem starTip_ball_gap {d R r ρ : ℕ} (hr : 0 < r) (b : Vertex d) (i j : Fin d)
    {z : Vertex d} (hz : z ∈ translateSites (starTip b j R) (centeredBox d (r - 1))) :
    (ρ : ℝ) + 1 ≤ latticeDistance (starTip b i (R + r + ρ)) z := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
  have hu' := (mem_centeredBox.mp hu i).2
  have hInt : (ρ : ℤ) + 1 ≤ starTip b i (R + r + ρ) i - (starTip b j R + u) i := by
    by_cases hij : i = j
    · subst j
      simp [starTip, coordinateRay, Pi.add_apply, Nat.cast_add]
      omega
    · simp [starTip, coordinateRay, Pi.add_apply, Nat.cast_add, hij]
      omega
  have hReal : (ρ : ℝ) + 1 ≤ (starTip b i (R + r + ρ) i : ℝ) -
      ((starTip b j R + u) i : ℝ) := by exact_mod_cast hInt
  exact hReal.trans ((le_abs_self _).trans (latticeDistance_coord_le _ _ i))

/-- The own moat contributes a tail from the backward ray, a contribution
from the other rays, and a bounded-volume contribution from the tip balls. -/
theorem ownMoat_green_mass_le {d : ℕ} (hd : 4 ≤ d)
    (b : Vertex d) (axes : Finset (Fin d)) (i : Fin d) (hi : i ∈ axes)
    (R r ρ : ℕ) (hr : 0 < r) (hρ : 0 < ρ) :
    (∑ z ∈ branchMoatVertices b axes R r, moatGreen (starTip b i (R + r + ρ)) z) ≤
      1 / (ρ : ℝ) + (axes.card : ℝ) / ((R : ℝ) + (r : ℝ)) +
        (axes.card : ℝ) * (((2 * (r - 1) + 1) ^ d : ℕ) : ℝ) / ((ρ : ℝ) + 1)^2 := by
  let N := R + r
  let a := starTip b i (N + ρ)
  let g := moatGreen a
  let Rays := fun j : Fin d => (Finset.range N).image (starTip b j)
  let Balls := fun j : Fin d => translateSites (starTip b j R) (centeredBox d (r - 1))
  have hN : (0 : ℝ) < N := by exact_mod_cast (by dsimp [N]; omega : 0 < N)
  have hg (z : Vertex d) : 0 ≤ g z := moatGreen_nonneg _ _
  have hsub : starNonTipVertices b axes (R + r) ⊆ axes.biUnion Rays := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
  have hray (j : Fin d) : (∑ z ∈ Rays j, g z) ≤ ∑ k ∈ Finset.range N, g (starTip b j k) :=
    Finset.sum_image_le_of_nonneg (fun z _ => hg z)
  have hown : (∑ z ∈ Rays i, g z) ≤ 1 / (ρ : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, g (starTip b i k) := hray i
      _ ≤ ∑ k ∈ Finset.range N, 1 / ((ρ : ℝ) + ((N - k : ℕ) : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have hs : (1 : ℝ) ≤ (ρ : ℝ) + ((N - k : ℕ) : ℝ) := by
          have h1 : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
          exact h1.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
        apply moatGreen_le_invSq hd hs
        have hgap := starTip_same_ray_gap b i (N + ρ) k
        change (ρ : ℝ) + ((N - k : ℕ) : ℝ) ≤ latticeDistance a (starTip b i k)
        rw [Nat.cast_sub (by omega : k ≤ N)]
        push_cast at hgap
        exact (by linarith : (ρ : ℝ) + ((N : ℝ) - (k : ℝ)) ≤
          ((N : ℝ) + (ρ : ℝ)) - (k : ℝ)).trans hgap
      _ ≤ _ := (finite_invSq_tail N ρ hρ).trans (sub_le_self _ (by positivity))
  have hother (j : Fin d) (hij : i ≠ j) : (∑ z ∈ Rays j, g z) ≤ 1 / (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (by dsimp [N]; omega : 1 ≤ N)
    calc
      _ ≤ ∑ k ∈ Finset.range N, g (starTip b j k) := hray j
      _ ≤ ∑ _k ∈ Finset.range N, 1 / (N : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro k _
        apply moatGreen_le_invSq hd h1
        have hgap := starTip_other_ray_gap b hij (N + ρ) k
        exact (by exact_mod_cast Nat.le_add_right N ρ : (N : ℝ) ≤ ((N + ρ : ℕ) : ℝ)).trans hgap
      _ = 1 / (N : ℝ) := by simp; field_simp [ne_of_gt hN]
  have hstar : (∑ z ∈ starNonTipVertices b axes (R + r), g z) ≤
      1 / (ρ : ℝ) + (axes.card : ℝ) / (N : ℝ) := by
    calc
      _ ≤ ∑ z ∈ axes.biUnion Rays, g z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hg z)
      _ ≤ ∑ j ∈ axes, ∑ z ∈ Rays j, g z := sum_biUnion_le_of_nonneg g hg axes Rays
      _ = (∑ j ∈ axes.erase i, ∑ z ∈ Rays j, g z) + ∑ z ∈ Rays i, g z :=
        (Finset.sum_erase_add _ _ hi).symm
      _ ≤ (∑ _j ∈ axes.erase i, 1 / (N : ℝ)) + 1 / (ρ : ℝ) := by
        exact add_le_add (Finset.sum_le_sum (fun j hj => hother j (Finset.mem_erase.mp hj).1.symm)) hown
      _ ≤ _ := by
        have hc : ((axes.erase i).card : ℝ) ≤ axes.card := by exact_mod_cast Finset.card_erase_le
        simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
        linarith [mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hN.le)]
  have hballs : (∑ z ∈ axes.biUnion Balls, g z) ≤
      (axes.card : ℝ) * (((2 * (r - 1) + 1) ^ d : ℕ) : ℝ) / ((ρ : ℝ) + 1)^2 := by
    refine (sum_biUnion_le_of_nonneg g hg axes Balls).trans ?_
    calc
      _ ≤ ∑ j ∈ axes, ∑ _z ∈ Balls j, 1 / ((ρ : ℝ) + 1)^2 := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro z hz
        exact moatGreen_le_invSq hd (by linarith [Nat.cast_nonneg (α := ℝ) ρ])
          (starTip_ball_gap hr b i j hz)
      _ = _ := by
        simp [Balls, card_translateSites, card_centeredBox_exact, div_eq_mul_inv, mul_assoc]
  have hsum := (sum_union_le_of_nonneg g hg (starNonTipVertices b axes (R + r)) (axes.biUnion Balls)).trans
    (add_le_add hstar hballs)
  simpa only [branchMoatVertices, N, Nat.cast_add, g, a] using hsum

end NearCritical.SplitCrossDirect
