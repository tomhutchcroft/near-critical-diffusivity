module

public import NearCritical.Section8EnergyOneVarianceTermThree
public import NearCritical.Section8WeightedVarianceDiagrams
public import NearCritical.Section10SpanningCited

/-! Normalize the three Appendix-B variance sums by the actual heart-hit rate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory
open scoped Classical

/-- Terms one, two and four in the Appendix B normalization. The third term is
estimated separately because it uses the disjoint weighted mass. -/
def appendixVarianceSum {d : ℕ} (N : ℕ) (D : Finset (Vertex d)) (x : Vertex d)
    (g F : Vertex d → ℝ) (τ : Vertex d → Vertex d → ℝ) : ℝ :=
  (N : ℝ) ^ 3 * (∑ u ∈ D, ∑ w ∈ D, g w * τ w u * τ u x * F w * F u) +
  (N : ℝ) ^ 3 * (∑ u ∈ D, ∑ w ∈ D, g u * τ u w * τ u x * F w ^ 2) +
  (∑ w ∈ D, g w * F w ^ 2)

/-- If the heart-hit rate is at least `a / N³`, the branch-event bound gives a
conditional variance estimate with scale-independent multiplier `max (2/a) 1`.
The remainder is the bound for the normalized third diagram. -/
theorem heartCenteredMoment_le_appendixVarianceSum {d : ℕ} (p : unitInterval)
    (Q H : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ heartAnnulus Q H)
    (f : Vertex d → ℝ) (Z : Finset (Vertex d) → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hzero : ∀ y ∈ Q, y ∉ heartAnnulus Q H → f y = 0)
    (N : ℕ) (hN : 1 ≤ N) (a R : ℝ) (ha : 0 < a)
    (hbranch : heartCenteredMoment p Q H Z x ≤
      ∑ y ∈ Q, ∑ z ∈ Q, f y * f z * (percolation d p).real (heartBranchEvent Q H x y z)) :
    let D := heartAnnulus Q H
    let g := annulusG p Q H
    let τ := annulusTau p Q H
    let F (u : Vertex d) := ∑ y ∈ D, f y * τ u y
    a / (N : ℝ) ^ 3 ≤ g x →
    (∑ y ∈ D, f y * g y) * (∑ u ∈ D, g u * τ u x * F u) ≤ g x * R →
    heartCenteredMoment p Q H Z x ≤
      (percolation d p).real (heartEvent Q H x) *
        (max (2 / a) 1 * appendixVarianceSum N D x g F τ + R) := by
  intro D g τ F hhit hthird
  let B : ℝ := max (2 / a) 1
  let T₁ : ℝ := ∑ u ∈ D, ∑ w ∈ D, g w * τ w u * τ u x * F w * F u
  let T₂ : ℝ := ∑ u ∈ D, ∑ w ∈ D, g u * τ u w * τ u x * F w ^ 2
  let T₄ : ℝ := ∑ w ∈ D, g w * F w ^ 2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := pow_pos hNpos 3
  have hg (v : Vertex d) : 0 ≤ g v := measureReal_nonneg
  have hτ (u v : Vertex d) : 0 ≤ τ u v := measureReal_nonneg
  have hF (u : Vertex d) : 0 ≤ F u :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hf y) (hτ u y)
  have hT₁ : 0 ≤ T₁ := by
    dsimp only [T₁]
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun w _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hg w) (hτ w u)) (hτ u x)) (hF w)) (hF u)
  have hT₂ : 0 ≤ T₂ := by
    dsimp only [T₂]
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun w _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (hg u) (hτ u w)) (hτ u x)) (sq_nonneg _)
  have hT₄ : 0 ≤ T₄ := by
    dsimp only [T₄]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (hg w) (sq_nonneg _)
  have hB : 1 ≤ B := le_max_right _ _
  have hscale : 2 ≤ g x * B * (N : ℝ) ^ 3 := by
    have haB : 2 ≤ B * a := (div_le_iff₀ ha).mp (le_max_left _ _)
    have hag : a ≤ g x * (N : ℝ) ^ 3 := (div_le_iff₀ hN3).mp hhit
    calc
      2 ≤ B * a := haB
      _ ≤ B * (g x * (N : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hag (by linarith)
      _ = g x * B * (N : ℝ) ^ 3 := by ring
  have hfour := weighted_heartBranch_le_four_sums p Q H x hx f hf hzero
  change (∑ y ∈ Q, ∑ z ∈ Q, f y * f z * (percolation d p).real (heartBranchEvent Q H x y z)) ≤
    2 * T₁ + T₂ + (∑ y ∈ D, f y * g y) * (∑ u ∈ D, g u * τ u x * F u) + g x * T₄ at hfour
  have heq : (percolation d p).real (heartEvent Q H x) = g x :=
    heart_probability_eq_annulus p Q H x hx
  rw [heq]
  change _ ≤ g x * (B * ((N : ℝ) ^ 3 * T₁ + (N : ℝ) ^ 3 * T₂ + T₄) + R)
  refine hbranch.trans (hfour.trans ?_)
  calc
    _ ≤ (g x * B * (N : ℝ) ^ 3) * T₁ + (g x * B * (N : ℝ) ^ 3) * T₂ +
        g x * R + (g x * B) * T₄ := by
      apply add_le_add
      · exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hscale hT₁)
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (show 1 ≤ g x * B * (N : ℝ) ^ 3 by linarith) hT₂)) hthird
      · exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hB (hg x)) hT₄
    _ = _ := by ring

/-- For ERE1 the third-diagram remainder already has uniform cutoff decay.
The remaining bound needed is on the three Appendix-B sums. -/
theorem energyOne_centeredMoment_le_appendixVarianceSum {k : ℕ} (hk : 7 ≤ k)
    (C B G A : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i B)
    (green : CriticalSupGreenUpper (k + 1) G) (ordinary : OrdinaryArmWindowInput (k + 1) A)
    (ρ a : ℝ) (hρ : 0 < ρ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N L H : ℕ), 1 ≤ N → 1 ≤ H → 2 * L ≤ N → H ≤ L →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H → (H : ℝ) ≤ ρ * N →
      ∀ (excluded : Finset (Vertex (k + 1))), centeredBox (k + 1) L ⊆ excluded →
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      let D := heartAnnulus Q heart
      let p := criticalPoint (k + 1)
      let g := annulusG p Q heart
      let τ := annulusTau p Q heart
      ∀ x ∈ D, latticeDistance 0 x = N → ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ^ (k - 5) ≤ (N : ℝ) ^ (k - 6) →
      a * ρ ^ (k - 3) / (N : ℝ) ^ 3 ≤ g x →
      let F (u : Vertex (k + 1)) := ∑ y ∈ D, energyOneWeight excluded r x y * τ u y
      heartCenteredMoment p Q heart (fun S => regularityEnergyOne S excluded r x) x ≤
        (percolation (k + 1) p).real (heartEvent Q heart x) *
          (max (2 / (a * ρ ^ (k - 3))) 1 * appendixVarianceSum N D x g F τ +
            K / (r : ℝ) ^ (k - 5)) := by
  obtain ⟨K, hK, hterm⟩ := energyOne_variance_term_three_le hk C B G A hC hB hG hA
    panis arm green ordinary ρ a hρ ha
  refine ⟨K, hK, ?_⟩
  intro N L H hN hH hL hHL hgap hround excluded hex Q heart D p g τ x hx hxN r hr hs hhit F
  have hHQ : heart ⊆ Q := Section10.centeredBox_mono (by omega : H ≤ N)
  have hHex : heart ⊆ excluded := (Section10.centeredBox_mono hHL).trans hex
  have hq : 0 < (percolation (k + 1) p).real (heartEvent Q heart x) := by
    rw [show (percolation (k + 1) p).real (heartEvent Q heart x) = g x from
      heart_probability_eq_annulus p Q heart x hx]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact lt_of_lt_of_le (by positivity) hhit
  have hzero : ∀ y ∈ Q, y ∉ D → energyOneWeight excluded r x y = 0 := by
    intro y hy hyD
    have hyH : y ∈ heart := by
      by_contra hn
      exact hyD (Finset.mem_sdiff.mpr ⟨hy, fun hm => hn (Finset.mem_sdiff.mp hm).1⟩)
    have hmem : y ∈ excluded := hHex hyH
    simp [energyOneWeight, hmem]
  exact heartCenteredMoment_le_appendixVarianceSum p Q heart x hx
    (energyOneWeight excluded r x) (fun S => regularityEnergyOne S excluded r x)
    (energyOneWeight_nonneg excluded r x) hzero N hN
    (a * ρ ^ (k - 3)) (K / (r : ℝ) ^ (k - 5)) (by positivity)
    (energyOne_centeredMoment_le_branches p Q heart excluded hHQ r x hq) hhit
    (hterm N L H hN hH hL hHL hgap hround excluded hex x hx hxN r hr hs hhit)

end NearCritical.Section8
