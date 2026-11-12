module
public import NearCritical.Section8ExtensionConnectionLower
public import NearCritical.Section8ExtensionErrorBudget
public import NearCritical.Section8ExtensionSourceSurgery

/-! Source prop.extension from actual surgery, literal energies and the cited
restricted rectangle lower theorem. No unique-extension estimate is an input. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

private theorem extension_positive_reveal_left_subset {d : ℕ} (p : unitInterval)
    (Q H Q₃ H₃ F F₃ : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent Q H Q₃ H₃ F F₃) ≠ 0) : F ⊆ Q := by
  by_contra hbad
  have he : section9RevealEvent Q H Q₃ H₃ F F₃ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    apply hbad
    rw [← hω.1]
    exact heartClusterUnion_subset ω Q H
  exact hpos (by rw [he,measure_empty])

/-- Unique extension at the actual source positive face. Delta is fixed
before r; the positive lower coefficient may depend on r but is uniform in
scale, direction, revealed heart data, regular point and middle-core target.
The sole additional literature input is the fixed-shape rectangle theorem. -/
theorem section8_source_unique_extension {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H H₃ F F₃ boundary : Finset (Vertex d)) (x z : Vertex d),
      H ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F F₃) ≠ 0 →
      x ∈ section8ExtensionPositiveFaceCore i n → z ∈ section8ExtensionMiddleCore i n →
      sourceRegularPoint F (section8ExtensionSmallCube i n) boundary r δ x →
      let Q := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let T := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let ν := section9RevealedLaw (criticalPoint d) Q H Q₃ H₃ F F₃
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
        ν.real (section9AvoidanceEvent T T Q F {z} ((F ∩ boundary) \ {x}) x) := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  obtain ⟨c₀,hc₀,hbase⟩ := section8_extension_source_connection_lower (by omega : 2 ≤ d) rectangle
  let Cb : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let K₁ : ℝ := G^2*(4 : ℝ)^((d : ℝ)-2)
  let K₂ : ℝ := G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂,Cb]; positivity
  let D : ℝ := K₁+K₂+1
  have hD : 0 < D := by dsimp [D]; linarith
  let δ : ℝ := c₀/(4*D)
  have hδ : 0 < δ := div_pos hc₀ (mul_pos (by norm_num) hD)
  have hDδ : D*δ = c₀/4 := by
    dsimp only [δ]
    field_simp [ne_of_gt hD] <;> ring
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨cs,hcs,hsurgery⟩ := section8_extension_source_surgery_positive_critical_coefficient
    (by omega : 2 < d) asymptotics r
  refine ⟨cs*(c₀/2),mul_pos hcs (div_pos hc₀ (by norm_num)),?_⟩
  intro i n hn H H₃ F F₃ boundary x z hH hH₃ hpos hx hz hreg Q Q₃ T ν
  have hF : F ⊆ Q := extension_positive_reveal_left_subset (criticalPoint d) Q H Q₃ H₃ F F₃ hpos
  have hW : F ∩ boundary ⊆ Q := Finset.inter_subset_left.trans hF
  let a := Function.update x i (x i+(r : ℤ))
  let N : ℝ := (n : ℝ)^((2 : ℝ)-(d : ℝ))
  let E₁ := regularityEnergyOne F (section8ExtensionSmallCube i n) r x
  let E₂ := regularityEnergyTwo F boundary r x
  have hE₁ : E₁ ≤ δ := hreg.2.1
  have hE₂ : E₂ ≤ δ := hreg.2.2
  have herror : K₁*E₁+K₂*E₂ ≤ c₀/2 := by
    calc
      _ ≤ K₁*δ+K₂*δ := add_le_add
        (mul_le_mul_of_nonneg_left hE₁ hK₁) (mul_le_mul_of_nonneg_left hE₂ hK₂)
      _ = (K₁+K₂)*δ := by ring
      _ ≤ D*δ := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hδ.le
      _ = c₀/4 := hDδ
      _ ≤ c₀/2 := by linarith
  have hbaseline := hbase i n r hn x z hx hz
  have hbudget := section8_extension_source_revealed_energy_budget (by omega : 5 ≤ d)
    hG.le green i n r hr hn F boundary H H₃ F₃ hF hH hH₃ hpos hx hz
  change c₀*N ≤ (percolation d (criticalPoint d)).real
    (connectionToSetEvent (T : Set (Vertex d)) a {z}) at hbaseline
  change (percolation d (criticalPoint d)).real
      (connectionToSetEvent (T : Set (Vertex d)) a {z}) ≤
    ν.real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) + N*(K₁*E₁+K₂*E₂) at hbudget
  have hN : 0 ≤ N := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hscaled := mul_le_mul_of_nonneg_left herror hN
  have hshift : (c₀/2)*N ≤ ν.real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) := by
    have hh := hbaseline.trans (hbudget.trans (add_le_add le_rfl hscaled))
    nlinarith only [hh]
  have hs := hsurgery i n hn H H₃ F F₃ (F ∩ boundary) x z hH hH₃ hpos hx hz hW
  calc
    _ = cs*((c₀/2)*N) := by dsimp only [N]; ring
    _ ≤ cs*ν.real (section9AvoidanceEvent T T Q F {z} (F ∩ boundary) a) :=
      mul_le_mul_of_nonneg_left hshift hcs.le
    _ ≤ _ := hs

end NearCritical
