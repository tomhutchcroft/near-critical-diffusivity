module

public import NearCritical.Section9CoalescenceCaseThree

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Factor the sprinkle weight out of the sum over actual distinct
Case 3 pivot candidates. The physical-bond map can identify reversals. -/
theorem section9_case_three_opened_sum {d : ℕ} (q : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (P : Finset (Vertex d × Vertex d)) (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) :
    let I := (P.product P).filter (fun ef => ef.1 ≠ ef.2)
    let A := fun ef : (Vertex d × Vertex d) × (Vertex d × Vertex d) =>
      {ω : Configuration d |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
        sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
          sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2}
    (∑ ef ∈ I, ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A ef ×ˢ {η | η (bond ef.1) = true ∧ η (bond ef.2) = true})) =
      (∑ ef ∈ I, (percolation d (criticalPoint d)).real (A ef)) * (q : ℝ)^2 := by
  intro I A
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ef hef
  have hmem : ef ∈ (P.product P).filter (fun ef => ef.1 ≠ ef.2) := hef
  obtain ⟨he, hf⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hmem).1
  exact section9_case_three_opened_probability q L R Q₁ F₁ Q₃ F₃ B x y ef.1 ef.2
    (bond ef.1) (bond ef.2) (hbond ef.1 he) (hbond ef.2 hf)

/-- Select the physical coordinate for every oriented middle candidate.
Outside the candidate set the map is arbitrary and is never used. -/
theorem section9_middle_candidate_bond_map {d : ℕ} (i : Fin d) (n : ℕ) :
    ∃ bond : (Vertex d × Vertex d) → Bond d,
      ∀ e ∈ orientedLatticePairs (section9FiniteMiddle i n),
        s((bond e).1, bondTip (bond e)) = s(e.1, e.2) := by
  let P := orientedLatticePairs (section9FiniteMiddle i n)
  have hex (e : Vertex d × Vertex d) (he : e ∈ P) :
      ∃ b : Bond d, s(b.1, bondTip b) = s(e.1, e.2) := by
    obtain ⟨b, _, h | h⟩ := ((mem_orientedLatticePairs _ _ _).mp he).2.2
    · exact ⟨b, Sym2.eq_iff.mpr (Or.inl ⟨h.1.symm, h.2.symm⟩)⟩
    · exact ⟨b, Sym2.eq_iff.mpr (Or.inr ⟨h.1.symm, h.2.symm⟩)⟩
  refine ⟨fun e => if he : e ∈ P then Classical.choose (hex e he) else (0, i), ?_⟩
  intro e he
  have heP : e ∈ P := he
  simpa only [dite_eq_left heP] using Classical.choose_spec (hex e heP)

/-- Sum the uniform per-root estimate over the two families of roots. -/
theorem section9_sum_root_pairs_le {d : ℕ} (A A' : Finset (Vertex d))
    (f : Vertex d → Vertex d → ℝ) (K : ℝ)
    (h : ∀ x ∈ A, ∀ y ∈ A', f x y ≤ K) :
    ∑ x ∈ A, ∑ y ∈ A', f x y ≤ (A.card : ℝ) * (A'.card : ℝ) * K := by
  calc
    _ ≤ ∑ x ∈ A, ∑ y ∈ A', K :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => h x hx y hy
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The opened Case 3 pivot sum for a single pair of roots has
the source exponent under a quadratic upper bound on the sprinkle rate. -/
theorem section9_case_three_opened_sum_scaled {d : ℕ} (hd : 2 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
    ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ) ^ (-2 : ℝ) →
    ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
    R ⊆ centeredBox d (3*n) → B ⊆ centeredBox d (3*n) →
    x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
    ∀ (bond : (Vertex d × Vertex d) → Bond d),
    (∀ e ∈ orientedLatticePairs (section9FiniteMiddle i n),
      s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) →
    let P := orientedLatticePairs (section9FiniteMiddle i n)
    let I := (P.product P).filter (fun ef => ef.1 ≠ ef.2)
    let A := fun ef : (Vertex d × Vertex d) × (Vertex d × Vertex d) =>
      {ω : Configuration d |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
        sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
          sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2}
    (∑ ef ∈ I, ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A ef ×ˢ {η | η (bond ef.1) = true ∧ η (bond ef.2) = true})) ≤
      (B.card : ℝ) * K * (n : ℝ) ^ (-(2 : ℝ) * (d : ℝ) + 6) := by
  obtain ⟨C, G, hC, hG, hprob⟩ := section9_case_three_probability_bound hd asymptotics
  let J : ℝ := 2 * (d : ℝ) * 3^(d-1)
  let H₀ := G * (1 + 49 * J)
  refine ⟨(C / 8 ^ ((2 : ℝ) - (d : ℝ)))^2 * (2 * (d : ℝ))^2 * H₀^3 * q₀^2, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B x y hR hB hx hy bond hbond
  dsimp only
  rw [section9_case_three_opened_sum q L R Q₁ F₁ Q₃ F₃ B x y _ bond hbond]
  let A := C * ((n : ℝ) / 8) ^ ((2 : ℝ) - (d : ℝ))
  let H := G * (1 + J * ((6*n : ℕ)+1 : ℝ)^2)
  let M := (2 * (d : ℝ)) * H
  have hH : 0 ≤ H := by dsimp [H, J]; positivity
  have hMass : H ≤ H₀ * (n : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    exact section9_case_three_mass_normalization hG.le (by dsimp [J]; positivity) hn
  have hs := section9_case_three_scaled_bound (d := d) (by exact_mod_cast hn)
    hC.le hH q.property.1 hMass hq
  calc
    _ ≤ ((B.card : ℝ) * ((A * M) * (A * M) * H)) * (q : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (hprob i n hn L R Q₁ F₁ Q₃ F₃ B x y hR hB hx hy)
        (sq_nonneg _)
    _ = (B.card : ℝ) * ((A * M) * (A * M) * H * (q : ℝ)^2) := by ring
    _ ≤ _ := by
      rw [mul_assoc (B.card : ℝ)]
      exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

/-- The contribution summed over both root families, in the product
law with the independent fresh sprinkle. -/
theorem section9_case_three_root_sum_scaled {d : ℕ} (hd : 2 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
    ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ) ^ (-2 : ℝ) →
    ∀ (L R Q₁ F₁ Q₃ F₃ B X Y : Finset (Vertex d)),
    R ⊆ centeredBox d (3*n) → B ⊆ centeredBox d (3*n) →
    X ⊆ section9FiniteEndCube i n 0 → Y ⊆ section9FiniteEndCube i n 0 →
    ∀ (bond : (Vertex d × Vertex d) → Bond d),
    (∀ e ∈ orientedLatticePairs (section9FiniteMiddle i n),
      s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) →
    let P := orientedLatticePairs (section9FiniteMiddle i n)
    let I := (P.product P).filter (fun ef => ef.1 ≠ ef.2)
    let A := fun (x y : Vertex d) (ef : (Vertex d × Vertex d) × (Vertex d × Vertex d)) =>
      {ω : Configuration d |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
        sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
          sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2}
    (∑ x ∈ X, ∑ y ∈ Y, ∑ ef ∈ I, ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A x y ef ×ˢ {η | η (bond ef.1) = true ∧ η (bond ef.2) = true})) ≤
      (X.card : ℝ) * (Y.card : ℝ) * ((B.card : ℝ) * K * (n : ℝ) ^ (-(2 : ℝ) * (d : ℝ) + 6)) := by
  obtain ⟨K, hK⟩ := section9_case_three_opened_sum_scaled hd asymptotics q₀
  refine ⟨K, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B X Y hR hB hX hY bond hbond
  dsimp only
  apply section9_sum_root_pairs_le X Y
  intro x hx y hy
  exact hK i n hn q hq L R Q₁ F₁ Q₃ F₃ B x y hR hB (hX hx) (hY hy) bond hbond

end NearCritical
