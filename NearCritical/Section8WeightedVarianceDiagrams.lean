module

public import NearCritical.Section8EnergyMoments
public import NearCritical.Section8FiveDiagrams

/-! Summing the actual five-diagram variance bound over the energy weights. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory
open scoped Classical

private theorem sum_weighted_separated {α ι : Type*} (D : Finset α) (J : Finset ι)
    (f : α → ℝ) (a : ι → ℝ) (b c : ι → α → ℝ) :
    (∑ y ∈ D, ∑ z ∈ D, f y * f z * (∑ j ∈ J, a j * b j y * c j z)) =
      ∑ j ∈ J, a j * (∑ y ∈ D, f y * b j y) * (∑ z ∈ D, f z * c j z) := by
  simp only [Finset.mul_sum, Finset.sum_mul] at *
  calc
    _ = ∑ y ∈ D, ∑ j ∈ J, ∑ z ∈ D, f y * f z * (a j * b j y * c j z) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ j ∈ J, ∑ y ∈ D, ∑ z ∈ D, f y * f z * (a j * b j y * c j z) := Finset.sum_comm
    _ = ∑ j ∈ J, ∑ z ∈ D, ∑ y ∈ D, (a j * (f y * b j y)) * (f z * c j z) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- The weighted actual branch-event sum has the four terms of the source
variance proof. The first two diagrams contribute the same folded term. -/
theorem weighted_heartBranch_le_four_sums {d : ℕ} (p : unitInterval)
    (Q H : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ heartAnnulus Q H)
    (f : Vertex d → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hzero : ∀ y ∈ Q, y ∉ heartAnnulus Q H → f y = 0) :
    let D := heartAnnulus Q H
    let g := annulusG p Q H
    let τ := annulusTau p Q H
    let F (u : Vertex d) := ∑ y ∈ D, f y * τ u y
    let ρ := ∑ y ∈ D, f y * g y
    (∑ y ∈ Q, ∑ z ∈ Q, f y * f z * (percolation d p).real (heartBranchEvent Q H x y z)) ≤
      2 * (∑ u ∈ D, ∑ w ∈ D, g w * τ w u * τ u x * F w * F u) +
      (∑ u ∈ D, ∑ w ∈ D, g u * τ u w * τ u x * F w ^ 2) +
      ρ * (∑ u ∈ D, g u * τ u x * F u) +
      g x * (∑ w ∈ D, g w * F w ^ 2) := by
  intro D g τ F ρ
  let J := D ×ˢ D
  let p₁ (y z : Vertex d) := ∑ j ∈ J,
    (g j.2 * τ j.2 j.1 * τ j.1 x) * τ j.2 y * τ j.1 z
  let p₂ (y z : Vertex d) := ∑ j ∈ J,
    (g j.1 * τ j.1 j.2 * τ j.2 x) * τ j.2 y * τ j.1 z
  let p₃ (y z : Vertex d) := ∑ j ∈ J,
    (g j.1 * τ j.1 j.2 * τ j.1 x) * τ j.2 y * τ j.2 z
  let p₄ (y z : Vertex d) := ∑ u ∈ D, (g u * τ u x) * g y * τ u z
  let p₅ (y z : Vertex d) := ∑ w ∈ D, (g x * g w) * τ w y * τ w z
  let fold (B : Vertex d → Vertex d → ℝ) := ∑ y ∈ D, ∑ z ∈ D, f y * f z * B y z
  have hD := heartAnnulus_subset Q H
  have hrestrict : (∑ y ∈ Q, ∑ z ∈ Q, f y * f z * (percolation d p).real (heartBranchEvent Q H x y z)) =
      ∑ y ∈ D, ∑ z ∈ D, f y * f z * (percolation d p).real (heartBranchEvent Q H x y z) := by
    rw [← Finset.sum_subset hD (fun y hy hny => by simp [hzero y hy hny])]
    apply Finset.sum_congr rfl
    intro y _
    exact (Finset.sum_subset hD (fun z hz hnz => by simp [hzero z hz hnz])).symm
  have hdiag (y z : Vertex d) (hy : y ∈ D) (hz : z ∈ D) :
      (percolation d p).real (heartBranchEvent Q H x y z) ≤ p₁ y z + p₂ y z + p₃ y z + p₄ y z + p₅ y z := by
    have h := heartBranch_probability_le_five_diagrams p Q H x y z hx hy hz
    refine h.trans (le_of_eq ?_)
    dsimp only [p₁, p₂, p₃, p₄, p₅, J]
    simp only [Finset.sum_product, Finset.mul_sum]
    congr 1
    · congr 1
      · congr 1
        · congr 1 <;> (apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro w _; ring)
        · apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro w _
          ring
      · apply Finset.sum_congr rfl
        intro u _
        ring
    · apply Finset.sum_congr rfl
      intro w _
      ring
  have h₁ : fold p₁ = ∑ u ∈ D, ∑ w ∈ D, g w * τ w u * τ u x * F w * F u := by
    simpa only [fold, p₁, J, F, Finset.sum_product] using
      sum_weighted_separated D J f (fun j => g j.2 * τ j.2 j.1 * τ j.1 x)
        (fun j y => τ j.2 y) (fun j z => τ j.1 z)
  have h₂ : fold p₂ = fold p₁ := by
    rw [h₁]
    calc
      _ = ∑ u ∈ D, ∑ w ∈ D, g u * τ u w * τ w x * F w * F u := by
        simpa only [fold, p₂, J, F, Finset.sum_product] using
          sum_weighted_separated D J f (fun j => g j.1 * τ j.1 j.2 * τ j.2 x)
            (fun j y => τ j.2 y) (fun j z => τ j.1 z)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro w _
        ring
  have h₃ : fold p₃ = ∑ u ∈ D, ∑ w ∈ D, g u * τ u w * τ u x * F w ^ 2 := by
    simpa only [fold, p₃, J, F, Finset.sum_product, pow_two, mul_assoc] using
      sum_weighted_separated D J f (fun j => g j.1 * τ j.1 j.2 * τ j.1 x)
        (fun j y => τ j.2 y) (fun j z => τ j.2 z)
  have h₄ : fold p₄ = ρ * (∑ u ∈ D, g u * τ u x * F u) := by
    calc
      _ = ∑ u ∈ D, g u * τ u x * ρ * F u := by
        exact sum_weighted_separated D D f (fun u => g u * τ u x) (fun _ y => g y) τ
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
  have h₅ : fold p₅ = g x * (∑ w ∈ D, g w * F w ^ 2) := by
    calc
      _ = ∑ w ∈ D, g x * g w * F w * F w :=
        sum_weighted_separated D D f (fun w => g x * g w) τ τ
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
  rw [hrestrict]
  calc
    _ ≤ ∑ y ∈ D, ∑ z ∈ D, f y * f z * (p₁ y z + p₂ y z + p₃ y z + p₄ y z + p₅ y z) :=
      Finset.sum_le_sum (fun y hy => Finset.sum_le_sum (fun z hz =>
        mul_le_mul_of_nonneg_left (hdiag y z hy hz) (mul_nonneg (hf y) (hf z))))
    _ = fold p₁ + fold p₂ + fold p₃ + fold p₄ + fold p₅ := by
      simp only [fold, mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [h₂, h₁, h₃, h₄, h₅]; ring

end NearCritical.Section8
