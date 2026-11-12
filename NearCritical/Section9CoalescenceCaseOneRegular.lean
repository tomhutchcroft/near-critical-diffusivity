module

public import NearCritical.Section9CoalescenceCaseOneScale

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Sum the shared-left event over the two regular root families. -/
theorem section9_case_one_regular_sum_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) :
    ∃ C : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y S boundary : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        (∀ x ∈ X, sourceRegularPoint F₁ S boundary r δ x) →
        (∀ y ∈ Y, sourceRegularPoint F₁ S boundary r δ y) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        (∑ x ∈ X, ∑ y ∈ Y, μ.real {ξη |
          (sprinklingUnexploredCluster ξη.1 L Q₁ F₁ x ∩
            sprinklingUnexploredCluster ξη.1 L Q₁ F₁ y).Nonempty ∧
          (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B).Nonempty}) ≤
          C * (B.card : ℝ) * (min X.card Y.card : ℕ) *
            (n:ℝ)^((2:ℝ)-(d:ℝ)) := by
  obtain ⟨A, G, hA, hG, h⟩ := section9_case_one_revealed_event_le hd asymptotics
  let J : ℝ := 2 * (d : ℝ) * 3^(d-1)
  let M₀ := (2 * (d : ℝ)) * (G * (1 + 49 * J))
  let K₀ := G^2 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*J))
  let C₀ := ((M₀ * q₀) * (A / 8^((2:ℝ)-(d:ℝ)))) * K₀
  refine ⟨C₀ * ((r:ℝ)^((d:ℝ)-4) * δ), ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y S boundary hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hB hX hY P μ
  let M := (2 * (d : ℝ)) * (G * (1 + J * ((6*n : ℕ)+1 : ℝ)^2))
  let W := fun (x y : Vertex d) => (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ))
  let T := (B.card : ℝ) * C₀ * (n:ℝ)^((2:ℝ)-(d:ℝ))
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq₀ : 0 ≤ q₀ := nonneg_of_mul_nonneg_left (q.property.1.trans hq)
    (Real.rpow_pos_of_pos hn' _)
  have hT : 0 ≤ T := by dsimp [T, C₀, M₀, K₀, J]; positivity
  have hMass : M ≤ M₀ * (n:ℝ)^(2:ℝ) := by
    rw [Real.rpow_two]
    dsimp only [M, M₀]
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hD : 0 ≤ 2 * (d : ℝ) := by positivity
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (section9_case_three_mass_normalization hG.le hJ hn) hD
  calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ Y, T * W x y := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      refine (h i n hn q L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hB x y).trans ?_
      have hs := section9_case_one_scale_factors (d := d) (N := (B.card : ℝ)) hn' hA.le
        (by dsimp [M, J]; positivity) q.property.1 (Nat.cast_nonneg _)
        (show 0 ≤ K₀ * W x y by dsimp [K₀, J, W]; positivity) hMass hq
      refine (le_of_eq ?_).trans (hs.trans_eq ?_)
      · dsimp only [M, K₀, J, W]
        push_cast
        ring
      · dsimp only [T, C₀, K₀, J, W]
        ring
    _ = T * (∑ x ∈ X, ∑ y ∈ Y, W x y) := by simp only [Finset.mul_sum]
    _ ≤ T * ((min X.card Y.card : ℕ) * ((r:ℝ)^((d:ℝ)-4) * δ)) :=
      mul_le_mul_of_nonneg_left
        (section9_regular_bubble_pair_sum_le ((by decide : 4 ≤ 5).trans hd)
          F₁ S boundary X Y r hr δ hX hY) hT
    _ = _ := by dsimp only [T]; ring

/-- Macroscopic separation bounds every root-pair kernel by one
uniform power, yielding the improved coalescence exponent. -/
theorem section9_separated_bubble_pair_sum_le {d : ℕ} (hd : 4 ≤ d)
    (X Y : Finset (Vertex d)) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, r ≤ latticeDistance x y) :
    (∑ x ∈ X, ∑ y ∈ Y, (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ))) ≤
      (X.card : ℝ) * (Y.card : ℝ) * r ^ ((4:ℝ)-(d:ℝ)) := by
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  apply section9_sum_root_pairs_le X Y
  intro x hx y hy
  exact Real.rpow_le_rpow_of_nonpos hr ((hsep x hx y hy).trans (le_max_right _ _))
    (sub_nonpos.mpr hd')

/-- Case 1 with macroscopic root separation gives the improved
coalescence rate without a regularity row bound. -/
theorem section9_case_one_separated_sum_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        (∀ x ∈ X, ∀ y ∈ Y, c * (n:ℝ) ≤ latticeDistance x y) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        (∑ x ∈ X, ∑ y ∈ Y, μ.real {ξη |
          (sprinklingUnexploredCluster ξη.1 L Q₁ F₁ x ∩
            sprinklingUnexploredCluster ξη.1 L Q₁ F₁ y).Nonempty ∧
          (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B).Nonempty}) ≤
          C * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) *
            (n:ℝ)^(6 - 2 * (d:ℝ)) := by
  obtain ⟨A, G, hA, hG, h⟩ := section9_case_one_revealed_event_le hd asymptotics
  let J : ℝ := 2 * (d : ℝ) * 3^(d-1)
  let M₀ := (2 * (d : ℝ)) * (G * (1 + 49 * J))
  let K₀ := G^2 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*J))
  let C₀ := ((M₀ * q₀) * (A / 8^((2:ℝ)-(d:ℝ)))) * K₀
  refine ⟨C₀ * c^((4:ℝ)-(d:ℝ)), ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hB hsep P μ
  let M := (2 * (d : ℝ)) * (G * (1 + J * ((6*n : ℕ)+1 : ℝ)^2))
  let W := fun (x y : Vertex d) => (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ))
  let T := (B.card : ℝ) * C₀ * (n:ℝ)^((2:ℝ)-(d:ℝ))
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hq₀ : 0 ≤ q₀ := nonneg_of_mul_nonneg_left (q.property.1.trans hq)
    (Real.rpow_pos_of_pos hn' _)
  have hT : 0 ≤ T := by dsimp [T, C₀, M₀, K₀, J]; positivity
  have hMass : M ≤ M₀ * (n:ℝ)^(2:ℝ) := by
    rw [Real.rpow_two]
    dsimp only [M, M₀]
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hD : 0 ≤ 2 * (d : ℝ) := by positivity
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (section9_case_three_mass_normalization hG.le hJ hn) hD
  calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ Y, T * W x y := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      refine (h i n hn q L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hB x y).trans ?_
      have hs := section9_case_one_scale_factors (d := d) (N := (B.card : ℝ)) hn' hA.le
        (by dsimp [M, J]; positivity) q.property.1 (Nat.cast_nonneg _)
        (show 0 ≤ K₀ * W x y by dsimp [K₀, J, W]; positivity) hMass hq
      refine (le_of_eq ?_).trans (hs.trans_eq ?_)
      · dsimp only [M, K₀, J, W]
        push_cast
        ring
      · dsimp only [T, C₀, K₀, J, W]
        ring
    _ = T * (∑ x ∈ X, ∑ y ∈ Y, W x y) := by simp only [Finset.mul_sum]
    _ ≤ T * ((X.card : ℝ) * (Y.card : ℝ) * (c * (n:ℝ))^((4:ℝ)-(d:ℝ))) :=
      mul_le_mul_of_nonneg_left
        (section9_separated_bubble_pair_sum_le ((by decide : 4 ≤ 5).trans hd)
          X Y (mul_pos hc hn') hsep) hT
    _ = _ := by
      dsimp only [T]
      rw [Real.mul_rpow hc.le hn'.le]
      have he : (n:ℝ)^((2:ℝ)-(d:ℝ)) * (n:ℝ)^((4:ℝ)-(d:ℝ)) =
          (n:ℝ)^(6 - 2 * (d:ℝ)) := by
        rw [← Real.rpow_add hn']
        congr 1
        ring
      rw [← he]
      ring

end NearCritical
