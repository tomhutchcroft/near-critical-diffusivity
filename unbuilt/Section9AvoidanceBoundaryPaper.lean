module
public import NearCritical.Section9AvoidanceWeightedComparison
public import NearCritical.Section9CandidateFiberUpper
public import NearCritical.Section9AvoidanceComparison
public import NearCritical.Section9AvoidanceNormalization
public import NearCritical.Section9OrientedClusterBoundary

/-! The source avoidance bound on the full actual oriented cluster boundary. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Full source boundary indexing, including zero-energy cases. The proof
pads suffix masses only internally, never in the actual public probability sum. -/
theorem section9_source_avoidance_boundary_paper {d : ℕ} (hd : 9 ≤ d)
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
      let P := section9OrientedClusterBoundary i n C
      let w := fun t : Vertex d × Vertex d =>
        ∑ z ∈ Z, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) z {t.1})
      let q := fun t : Vertex d × Vertex d =>
        ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.2)
      0 < ν.real E →
      (((B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ)))/U) *
        (max (c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(V.card : ℝ)) 0)^2 * (Z.card : ℝ)^2 /
          (∑ t ∈ P, (w t)^2) ≤ ∑ t ∈ P, q t / ν.real E := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  let U : ℝ := G*(16 : ℝ)^((d : ℝ)-2)
  have hU : 0 < U := mul_pos hG (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨δ,hδ,hweighted⟩ := section9_source_avoidance_weighted_comparison hd asymptotics rectangle reimer
  refine ⟨U,hU,δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,K,hK,hbound⟩ := hweighted r hr
  refine ⟨c,hc,K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B C Z root hH₁ hH₃ hpos hroot hCL hB hregular hZM hZC
    Q₁ Q₃ L R V ν E P w q hm
  let J := section9AvoidanceLastExitCandidates R C Q₃ F₃
  let I := J.image (fun t : (Vertex d × Vertex d) × Bond d => t.1)
  let ppad := fun e : Vertex d × Vertex d => if e ∈ I then q e/ν.real E else 0
  have hq0 (e : Vertex d × Vertex d) : 0 ≤ q e/ν.real E :=
    div_nonneg measureReal_nonneg hm.le
  by_cases hBempty : B = ∅
  · simp only [hBempty,Finset.card_empty,Nat.cast_zero,zero_mul,zero_div]
    exact Finset.sum_nonneg fun e _ => hq0 e
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcard : 0 < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hBempty)
  let s : ℝ := (B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))
  let t : ℝ := c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(V.card : ℝ)
  let a : ℝ := U*s
  let T : ℝ := (c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) -
    (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ)))*(Z.card : ℝ)
  have hs : 0 < s := mul_pos hcard (Real.rpow_pos_of_pos hn0 _)
  have ha : 0 < a := mul_pos hU hs
  have hZ : 0 ≤ (Z.card : ℝ) := Nat.cast_nonneg _
  have hTfactor : T = s*t*(Z.card : ℝ) := by
    dsimp only [T,s,t]
    rw [section9_avoidance_error_power_factor d (n : ℝ) hn0]
    ring
  have hnum : a*(max (T/a) 0)^2 = (s/U)*(max t 0)^2*(Z.card : ℝ)^2 := by
    dsimp only [a]
    rw [hTfactor]
    exact section9_avoidance_normalized_numerator U s t (Z.card : ℝ) hU hs.le hZ
  have hinj := section9_last_exit_candidate_projection_injOn i n C F₃
  have hIP : I ⊆ P := section9_last_exit_candidate_projection_subset_boundary i n C F₃ hCL
  have hreindex : (∑ j ∈ J, w j.1*(q j.1/ν.real E)) =
      ∑ e ∈ I, w e*(q e/ν.real E) := by
    dsimp only [I]
    exact (Finset.sum_image (fun j hj k hk heq => hinj hj hk heq)).symm
  have hpadsum : (∑ e ∈ I, w e*(q e/ν.real E)) = ∑ e ∈ P, w e*ppad e := by
    calc
      _ = ∑ e ∈ I, w e*ppad e := by
        apply Finset.sum_congr rfl
        intro e he
        simp only [ppad,if_pos he]
      _ = _ := Finset.sum_subset hIP (fun e _ he => by simp only [ppad,if_neg he,mul_zero])
  have hcomp := hbound i n hn H₁ H₃ F₁ F₃ boundary B C Z root
    hH₁ hH₃ hpos hroot hCL hB hregular hZM hZC
  change ν.real E*(c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) -
    (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ)))*(Z.card : ℝ) ≤
      ∑ j ∈ J, w j.1*q j.1 at hcomp
  have hweighted : T ≤ ∑ e ∈ P, w e*ppad e := by
    have hdiv : T ≤ (∑ j ∈ J, w j.1*q j.1)/ν.real E := by
      apply (le_div_iff₀ hm).mpr
      simpa only [T,mul_assoc,mul_left_comm,mul_comm] using hcomp
    have hsum : (∑ j ∈ J, w j.1*q j.1)/ν.real E =
        ∑ j ∈ J, w j.1*(q j.1/ν.real E) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum,hreindex,hpadsum] at hdiv
    exact hdiv
  have hp (e : Vertex d × Vertex d) (_heP : e ∈ P) : 0 ≤ ppad e ∧ ppad e ≤ a := by
    by_cases heI : e ∈ I
    · obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp heI
      have hu := section9_source_candidate_fiber_avoidance_upper (by omega : 2 ≤ d)
        hG.le green i n (by omega : 16 ≤ n) H₁ H₃ F₁ F₃ C B V root
        hH₁ hH₃ hpos hroot hCL hB j hj
      have hupper : q e/ν.real E ≤ a := by
        apply (div_le_iff₀ hm).mpr
        change q j.1 ≤ ν.real E*(G*(16 : ℝ)^((d : ℝ)-2)*(B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))) at hu
        rw [hje] at hu
        simpa only [a,s,U,mul_assoc,mul_left_comm,mul_comm] using hu
      simpa only [ppad,if_pos heI] using And.intro (hq0 e) hupper
    · simp only [ppad,if_neg heI]
      exact ⟨le_rfl,ha.le⟩
  have hscale : a*(T/a) = T := by field_simp [ne_of_gt ha]
  have hcompare : a*(T/a) ≤ ∑ e ∈ P, w e*ppad e := by rw [hscale]; exact hweighted
  have hscalar := section9Avoidance_positive_part_comparison P w ppad a (T/a) ha hp hcompare
  have hrhs : (∑ e ∈ P, ppad e) ≤ ∑ e ∈ P, q e/ν.real E := by
    apply Finset.sum_le_sum
    intro e _
    by_cases he : e ∈ I
    · simp only [ppad,if_pos he]
    · simpa only [ppad,if_neg he] using hq0 e
  rw [hnum] at hscalar
  simpa only [s,t] using hscalar.trans hrhs

end NearCritical
