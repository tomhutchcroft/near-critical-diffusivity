module

public import NearCritical.Section8AnnulusHeartHitLower
public import NearCritical.Section8EnergyTwoUniformVariance
public import NearCritical.Section10EnergyMeanTree
public import NearCritical.Section10MomentCubeGeometry

/-! The uniform variance hypothesis used in the pre-good cube proof. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open NearCritical.Section8 AppendixVariance MeasureTheory
open scoped Classical

/-- The integer exclusion used for the ERE1 estimates is contained in the
strict real exclusion of the actual marked cube. -/
theorem varianceCube_subset_typicalInnerCube {d : ℕ} (t : ℕ) (ht : 1 ≤ t) :
    (cube (3 * ((t - 1) / 2) / 4) : Finset (Vertex d)) ⊆ typicalInnerCube t (0 : Vertex d) := by
  let N := (t - 1) / 2
  let L := 3 * N / 4
  intro x hx
  have hxL : x ∈ centeredBox d L := by
    rw [← appendix_cube_eq_centeredBox]
    exact hx
  apply Finset.mem_filter.mpr
  refine ⟨?_, fun i => ?_⟩
  · rw [typicalCube_zero t ht]
    exact centeredBox_mono (show L ≤ N by dsimp [L]; omega) hxL
  · have h := mem_centeredBox.mp hxL i
    have habs : |(x i : ℝ)| ≤ (L : ℝ) :=
      abs_le.mpr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    have hlt : (8 : ℝ) * L < 3 * (t : ℝ) := by
      exact_mod_cast (show 8 * L < 3 * t by dsimp [L, N]; omega)
    simp only [Pi.zero_apply, sub_zero]
    linarith

/-- Both actual energy variances satisfy the pre-good bound on all marked
faces. The coefficient may depend on the heart ratio and is chosen before
the cutoff. The lower estimate for the box two-point function remains explicit. -/
theorem marked_conditional_variance_of_box_lower (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (C B S A : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hS : 0 ≤ S) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (e + 7), SlabBoundarySecondMomentUpper i S)
    (ordinary : OrdinaryArmWindowInput (e + 7) A) (c : ℝ) (hc : 0 < c)
    (hbox : ∀ (i : Fin (e + 7)) (R : ℕ) (x : Vertex (e + 7)), 1 ≤ R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ)) →
      ∀ y ∈ centeredBox (e + 7) R, R ≤ 2 * (R - linfDist 0 y) →
        c / (R : ℝ) ^ (e + 6) ≤ (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent (centeredBox (e + 7) R : Set (Vertex (e + 7))) x {y}))
    (cc : ℝ) (hcc : 0 < cc) (hcc1 : cc ≤ 1 / 32) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℕ, 1 ≤ r → ∃ t₀ : ℕ, ∀ t ≥ t₀,
      ∀ x ∈ typMark t (0 : Vertex (e + 7)),
      let Q := typicalCube t (0 : Vertex (e + 7))
      let H := typicalHeart t (0 : Vertex (e + 7)) cc
      let p := criticalPoint (e + 7)
      heartCenteredMoment p Q H (fun F => regularityEnergyOne F (typicalInnerCube t 0) r x) x +
        heartCenteredMoment p Q H (fun F => regularityEnergyTwo F (typicalBoundary t 0) r x) x ≤
        (K / (r : ℝ) ^ (e + 7 - 6)) * (percolation (e + 7) p).real
          {ω | x ∈ heartClusterUnion ω Q H} := by
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ e + 7) asymp
  obtain ⟨κ, hκ, hhit⟩ := annulusG_lower_at_pc_of_box_lower e asymp C hC panis c hc hbox
  let ρ := 2 * cc
  let a := κ / (4 : ℝ) ^ (e + 3)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨K₁, hK₁, hvar₁⟩ := energyOne_centeredMoment_le_uniform he C B S A G hC hB hS hA hG.le
    panis arm second ordinary asymp green ρ a hρ ha
  obtain ⟨K₂, hK₂, hvar₂⟩ := energyTwo_centeredMoment_le_uniform he C B S A hC hB hS hA
    panis arm second ordinary asymp ρ a hρ ha
  obtain ⟨t₁, _, ht₁⟩ := typicalMomentCube_eventually_scales cc hcc hcc1
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  intro r hr
  refine ⟨max 64 (max t₁ (4 * r ^ (e + 1) + 1)), ?_⟩
  intro t ht x hx Q H p
  let N := (t - 1) / 2
  let L := N / 2
  let h := typicalHeartRadius t cc
  have ht64 : 64 ≤ t := (le_max_left _ _).trans ht
  have hscale : max t₁ (4 * r ^ (e + 1) + 1) ≤ t := (le_max_right _ _).trans ht
  have hlarge : 2 * r ^ (e + 1) ≤ N := by
    have ht' := (le_max_right t₁ (4 * r ^ (e + 1) + 1)).trans hscale
    dsimp [N]
    omega
  obtain ⟨hN, hh, hL, hhL, h5, hgap, hlo, hhi⟩ := ht₁ t ((le_max_left _ _).trans hscale)
  have hrn : r ≤ N := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hp : (r : ℝ) ≤ (r : ℝ) ^ (e + 1) := by
      simpa only [pow_one] using (pow_le_pow_right₀ hr1 (show 1 ≤ e + 1 by omega))
    have hlarge' : 2 * (r : ℝ) ^ (e + 1) ≤ N := by exact_mod_cast hlarge
    exact_mod_cast (show (r : ℝ) ≤ N by linarith)
  have hQ : Q = centeredBox (e + 7) N := typicalCube_zero t (by omega)
  have hH : H = centeredBox (e + 7) h := typicalHeart_zero_eq_centeredBox t (by omega) cc hcc (by linarith)
  have hboundary := typicalBoundary_zero_eq_cubeBoundary (k := e + 6) t (by omega)
  have hxD : x ∈ heartAnnulus (centeredBox (e + 7) N) (centeredBox (e + 7) h) := by
    rw [← hQ, ← hH]
    exact typMark_mem_annulus t ht64 (by linarith) hx
  have hxN : linfDist 0 x = N := by
    have hxB := typMark_subset_boundary t 0 hx
    rw [hboundary] at hxB
    exact (Finset.mem_filter.mp hxB).2
  obtain ⟨i, hface, hmargin⟩ := typMark_face_margin t (by omega) hx
  have hhit' := hhit i N h x hh h5 hxN (hface.elim Or.inr Or.inl)
    (fun j hj => by linarith [hmargin j hj])
  have hnorm : a * ρ ^ (e + 3) / (N : ℝ) ^ 3 ≤
      annulusG p (centeredBox (e + 7) N) (centeredBox (e + 7) h) x := by
    have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcomp : ρ / 4 ≤ (h : ℝ) / (N : ℝ) := by
      apply (le_div_iff₀ hn0).mpr
      dsimp [ρ]
      linarith
    have hp := pow_le_pow_left₀ (show 0 ≤ ρ / 4 by positivity) hcomp (e + 3)
    have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ.le)
      (show 0 ≤ (N : ℝ) ^ 3 by positivity)
    calc
      _ = κ * (ρ / 4) ^ (e + 3) / (N : ℝ) ^ 3 := by dsimp [a]; rw [div_pow]; ring
      _ ≤ _ := hh'.trans hhit'
  have hv₁ := hvar₁ N L h r hN hr hrn hlarge hh hL h5 hgap hhi _
    (varianceCube_subset_typicalInnerCube t (by omega)) x hxD hxN hnorm
  have hv₂ := hvar₂ N L h r hN hr hrn hlarge hh hL h5 hgap hhi x hxD hxN hnorm
  have hsub : centeredBox (e + 7) h ⊆ centeredBox (e + 7) N := centeredBox_mono (by omega)
  have hEvent : heartEvent (centeredBox (e + 7) N) (centeredBox (e + 7) h) x =
      {ω | x ∈ heartClusterUnion ω (centeredBox (e + 7) N) (centeredBox (e + 7) h)} :=
    Set.ext fun ω => heartEvent_iff_union_member _ _ hsub x ω
  rw [hQ, hH, hboundary, ← hEvent, show e + 7 - 6 = e + 1 by omega, add_div]
  exact (add_le_add hv₁ hv₂).trans_eq (by ring)

end NearCritical.Section10
