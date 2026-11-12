module

public import NearCritical.Section9CoalescenceGeometry
public import NearCritical.Section9CoalescenceFactorization
public import NearCritical.Section9SeparatedTwoPoint

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Source middle-pivot diagram bound. The radius envelope covers the
right tube and the target roots, and the left arms use the first end cube. -/
theorem section9_case_three_probability_bound {d : ℕ} (hd : 2 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C G : ℝ, 0 < C ∧ 0 < G ∧
      ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
        R ⊆ centeredBox d (3*n) → B ⊆ centeredBox d (3*n) →
        x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let A := C * ((n:ℝ)/8) ^ ((2:ℝ)-(d:ℝ))
        let H := G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2)
        let M := (2 * (d : ℝ)) * H
        (∑ ef ∈ (P.product P).filter (fun ef => ef.1 ≠ ef.2),
          (percolation d (criticalPoint d)).real {ω |
            sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
            sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
            Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
              (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
            sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
              sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2}) ≤
          (B.card : ℝ) * ((A * M) * (A * M) * H) := by
  obtain ⟨C, hC, decay⟩ := section9TwoPoint_middle_end_bounds hd asymptotics
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics hd asymptotics
  refine ⟨C, G, hC, hG, ?_⟩
  intro i n hn L R Q₁ F₁ Q₃ F₃ B x y hR hB hx hy
  dsimp only
  refine (section9_shared_right_restricted_pivot_sum_le
    L R Q₁ F₁ Q₃ F₃ B x y (orientedLatticePairs (section9FiniteMiddle i n))).trans ?_
  let a := fun e : Vertex d × Vertex d =>
    (percolation d (criticalPoint d)).real (connectionToSetEvent (L : Set (Vertex d)) e.1 {x})
  let b := fun e : Vertex d × Vertex d =>
    (percolation d (criticalPoint d)).real (connectionToSetEvent (L : Set (Vertex d)) e.1 {y})
  refine (section9_case_three_factorization (orientedLatticePairs (section9FiniteMiddle i n))
    R B a b (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_nonneg)).trans ?_
  apply section9_factored_diagram_le _ R B a b
  · positivity
  · positivity
  · positivity
  · positivity
  · intro e he
    exact measureReal_nonneg
  · intro e he
    apply le_trans _ (decay i n hn e.1 ((mem_orientedLatticePairs _ _ _).mp he).1 x (Or.inl hx))
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro ω ⟨_, v, hv, _, hpath⟩
    have hvx : v = x := hv
    subst v
    have hle : restrictedGraph ω (L : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    exact hpath.mono hle
  · intro e he
    apply le_trans _ (decay i n hn e.1 ((mem_orientedLatticePairs _ _ _).mp he).1 y (Or.inl hy))
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro ω ⟨_, v, hv, _, hpath⟩
    have hvy : v = y := hv
    subst v
    have hle : restrictedGraph ω (L : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    exact hpath.mono hle
  · intro u hu
    calc
      _ = ∑ e ∈ orientedLatticePairs (section9FiniteMiddle i n), section9RightArm R u e.2 :=
        Finset.sum_congr rfl (fun e _ => section9RightArm_symm R e.2 u)
      _ ≤ _ := section9_middle_head_mass_le hd hG.le green i n R u (hR hu)
  · intro u hu
    exact section9_middle_head_mass_le hd hG.le green i n R u (hR hu)
  · intro z hz
    exact section9_restricted_arm_mass_le hd hG.le green _ R z (6*n) (fun u hu =>
      section9_distance_le_of_mem_centeredBox (hB hz) (hR hu))

/-- The two decay factors and three quadratic masses, multiplied by
the two fresh openings at scale n⁻², give the Case 3 exponent. -/
theorem section9_case_three_scale_product {d : ℕ} {n : ℝ} (hn : 0 < n) :
    (n ^ ((2 : ℝ) - (d : ℝ))) * n ^ ((2 : ℝ) - (d : ℝ)) *
      n ^ (2 : ℝ) * n ^ (2 : ℝ) * n ^ (2 : ℝ) *
      n ^ (-2 : ℝ) * n ^ (-2 : ℝ) =
        n ^ (-(2 : ℝ) * (d : ℝ) + 6) := by
  simp only [← Real.rpow_add hn]
  congr 1
  ring

/-- Convert the two-bond opening identity to real probabilities for
the finite diagram sums. -/
theorem section9_case_three_two_openings_real {d : ℕ} (q : unitInterval)
    (A : Set (Configuration d)) {e f : Bond d} (hef : e ≠ f) :
    ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A ×ˢ {η | η e = true ∧ η f = true}) =
        (percolation d (criticalPoint d)).real A * (q : ℝ)^2 := by
  rw [Measure.real, section9_critical_event_two_bond_opening (criticalPoint d) q A hef,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  rfl

/-- The shared-right pivot event itself excludes coincident physical bonds.
The conclusion holds before any fresh sprinkle bits are inspected. -/
theorem section9_case_three_physical_ne {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f)
    (hLL : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω L Q₁ F₁ f.1))
    (hshared : sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
      sprinklingUnexploredCluster ω R Q₃ F₃ f.2) :
    s(e.1,e.2) ≠ s(f.1,f.2) := by
  intro h
  have heL := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ he.2.1
  have hfL := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hf.2.1
  have heR := root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ he.2.2.1
  rcases Sym2.eq_iff.mp h with ⟨h₁, _⟩ | ⟨_, h₂⟩
  · exact Finset.disjoint_left.mp hLL heL (by simpa only [h₁] using hfL)
  · rw [hshared, h₂] at heR
    exact Finset.disjoint_left.mp hf.2.2.2.2.2 hfL heR

/-- The fresh opening factor applies to a Case 3 event even when
the candidate map is not globally injective on oriented pairs. -/
theorem section9_case_three_opened_probability {d : ℕ} (q : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d) (j k : Bond d)
    (hj : s(j.1, bondTip j) = s(e.1, e.2))
    (hk : s(k.1, bondTip k) = s(f.1, f.2)) :
    let A : Set (Configuration d) := {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2}
    ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A ×ˢ {η | η j = true ∧ η k = true}) =
        (percolation d (criticalPoint d)).real A * (q : ℝ)^2 := by
  intro A
  by_cases h : j = k
  · subst k
    have hempty : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨he, hf, hLL, hshared⟩ := hω
      exact section9_case_three_physical_ne ω L R Q₁ F₁ Q₃ F₃ B x y e f
        he hf hLL hshared (hj.symm.trans hk)
    simp [hempty]
  · exact section9_case_three_two_openings_real q A h

/-- Absorb the enumeration radius and the constant term into a
scale-independent multiple of n² for positive integer scales. -/
theorem section9_case_three_mass_normalization {G K : ℝ}
    (hG : 0 ≤ G) (hK : 0 ≤ K) {n : ℕ} (hn : 0 < n) :
    G * (1 + K * ((6*n : ℕ)+1 : ℝ)^2) ≤
      G * (1 + 49 * K) * (n : ℝ)^2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (6 * (n : ℝ) + 1)^2 ≤ 49 * (n : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (show 0 ≤ 13 * (n : ℝ) + 1 by positivity)]
  have hsq : (1 : ℝ) ≤ (n : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  push_cast
  calc
    _ ≤ G * ((n : ℝ)^2 + K * (49 * (n : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsq (mul_le_mul_of_nonneg_left hr hK)) hG
    _ = _ := by ring

/-- Absorb all scale-independent factors after the quadratic mass
and sprinkle-probability estimates have been supplied. -/
theorem section9_case_three_scaled_bound {d : ℕ} {n C H H₀ q q₀ : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hH : 0 ≤ H) (hq : 0 ≤ q)
    (hMass : H ≤ H₀ * n ^ (2 : ℝ)) (hSprinkle : q ≤ q₀ * n ^ (-2 : ℝ)) :
    let A := C * (n / 8) ^ ((2 : ℝ) - (d : ℝ))
    let M := (2 * (d : ℝ)) * H
    (A * M) * (A * M) * H * q^2 ≤
      (C / 8 ^ ((2 : ℝ) - (d : ℝ)))^2 * (2 * (d : ℝ))^2 * H₀^3 * q₀^2 *
        n ^ (-(2 : ℝ) * (d : ℝ) + 6) := by
  dsimp only
  rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8)]
  let A := C * (n ^ ((2 : ℝ) - (d : ℝ)) / 8 ^ ((2 : ℝ) - (d : ℝ)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMassNonneg : 0 ≤ H₀ * n ^ (2 : ℝ) := hH.trans hMass
  have hSprinkleNonneg : 0 ≤ q₀ * n ^ (-2 : ℝ) := hq.trans hSprinkle
  calc
    _ ≤ (A * ((2 * (d : ℝ)) * (H₀ * n ^ (2 : ℝ)))) *
        (A * ((2 * (d : ℝ)) * (H₀ * n ^ (2 : ℝ)))) *
        (H₀ * n ^ (2 : ℝ)) * (q₀ * n ^ (-2 : ℝ))^2 := by
      change (A * ((2 * (d : ℝ)) * H)) * (A * ((2 * (d : ℝ)) * H)) * H * q^2 ≤ _
      gcongr
    _ = _ := by
      rw [← section9_case_three_scale_product (d := d) hn]
      dsimp [A]
      ring

end NearCritical
