module
public import NearCritical.Section9SourceAvoidanceComparison
public import NearCritical.Section9AvoidanceNormalization

/-! Exact source numerator for the actual physical-candidate avoidance bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The actual candidate lower bound has the literal source positive-part
numerator. The full oriented-boundary index extension is a separate consumer. -/
theorem section9_source_avoidance_paper_form {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ U : ℝ, 0 < U ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary B C Z : Finset (Vertex d)) (root : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y) →
      Z ⊆ section8ExtensionMiddleCore i n → Z ⊆ C →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let V := section9ExitFace i n ∩ C
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
      let J := section9AvoidanceLastExitCandidates R C Q₃ F₃
      let w := fun t : (Vertex d × Vertex d) × Bond d =>
        ∑ z ∈ Z, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1})
      let q := fun t : (Vertex d × Vertex d) × Bond d =>
        ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2)
      0 < ν.real E →
      (((B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ)))/U) *
        (max (c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(V.card : ℝ)) 0)^2 * (Z.card : ℝ)^2 /
          (∑ t ∈ J, (w t)^2) ≤ ∑ t ∈ J, q t / ν.real E := by
  obtain ⟨U,hU,δ,hδ,hcomparison⟩ :=
    section9_source_avoidance_candidate_comparison hd asymptotics rectangle reimer
  refine ⟨U,hU,δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,K,hK,hbound⟩ := hcomparison r hr
  refine ⟨c,hc,K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B C Z root hH₁ hH₃ hpos hroot hCL hB hregular hZM hZC
    Q₁ Q₃ L R V ν E J w q hm
  have hraw := hbound i n hn H₁ H₃ F₁ F₃ boundary B C Z root
    hH₁ hH₃ hpos hroot hCL hB hregular hZM hZC hm
  let s : ℝ := (B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))
  let t : ℝ := c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(V.card : ℝ)
  let a : ℝ := U*(B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))
  let T : ℝ := (c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) -
    (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ)))*(Z.card : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)
  have hZ : 0 ≤ (Z.card : ℝ) := Nat.cast_nonneg _
  have ha : a = U*s := by dsimp only [a,s]; ring
  have hT : T = s*t*(Z.card : ℝ) := by
    dsimp only [T,s,t]
    rw [section9_avoidance_error_power_factor d (n : ℝ) hn0]
    ring
  have hnum : a*(max (T/a) 0)^2 = (s/U)*(max t 0)^2*(Z.card : ℝ)^2 := by
    rw [ha,hT]
    exact section9_avoidance_normalized_numerator U s t (Z.card : ℝ) hU hs hZ
  change a*(max (T/a) 0)^2/(∑ t ∈ J, (w t)^2) ≤ ∑ t ∈ J, q t/ν.real E at hraw
  rw [hnum] at hraw
  simpa only [s,t] using hraw

end NearCritical
