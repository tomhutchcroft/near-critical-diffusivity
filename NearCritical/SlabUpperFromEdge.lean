module

public import NearCritical.SlabCubeCorrespondence
public import NearCritical.Section10PreGoodEta

/-! prop.slab.upper from the cited inputs and the EDGE DATA only.

`exists_orParameter`: every `p >= a` with `a < 1` is `orParameter a s` for some `s`.

`slab_upper_of_edge`: in dimension `d >= 9`, from
* the cited inputs and moment package of the pre-good theorem
  (`Section10.pregood_of_moments_eta`),
* the cited planar mixed site-bond input for a law `κ` with
  `κ{true} <= 1 - η`,
* and the edge data `hedge`: for every `typ` with tolerance `δ` (and the positivity
  the pre-good theorem provides) there are a nest size `k > 0` and a sprinkle
  constant `lam > 0` (chosen AFTER `typ`, as the offspring estimate requires) such
  that for all large `n`, every sprinkle parameter `s`
  with `p_c or s = p_c + lam/n^2` and every box radius `R`: ambient bonds
  containing the cubes, a child-nest function that is local, succeeds with
  probability at least `κ{true}` for every parent nest and sample, and propagates
  the invariant `slabQ` from the parent endpoint to the far endpoint of the tube,

one gets `p_c(slab) - p_c <= C/n^2`. The site test, root nest, their bounds, the
invariant at the root, the join property, the resampled law, block independence,
the exploration domination and the translation to the actual slab are all
discharged here.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set Function
open scoped Classical ENNReal
open Section10

variable {d : ℕ}

lemma exists_orParameter (a p : I) (hap : (a : ℝ) ≤ (p : ℝ)) (ha1 : (a : ℝ) < 1) :
    ∃ s : I, orParameter a s = p := by
  have h1 : 0 < 1 - (a : ℝ) := by linarith
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  refine ⟨⟨((p : ℝ) - a) / (1 - a), div_nonneg (by linarith) h1.le,
    (div_le_one h1).mpr (by linarith)⟩, ?_⟩
  apply Subtype.ext
  change (a : ℝ) + (1 - (a : ℝ)) * (((p : ℝ) - a) / (1 - a)) = p
  have : (1 - (a : ℝ)) * (((p : ℝ) - a) / (1 - a)) = p - a := by field_simp
  linarith

set_option maxHeartbeats 1600000 in
theorem slab_upper_of_edge {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1)
    (hc : 0 < c) (ha₁' : 0 < a₁) (ha₂' : 0 < a₂) (ha₃' : 0 < a₃)
    {η δ : ℝ} (hη : 0 < η) (hδ0 : 0 < δ)
    (hmom : ∃ cc : ℝ, 0 < cc ∧ cc ≤ 1 / 16 ∧ ∃ Cm Cp Cb : ℝ, 0 ≤ Cm ∧ 0 ≤ Cp ∧ 0 ≤ Cb ∧
      ∃ rstar : ℕ, ∀ typ : TypicalParameters, typ.heartRatio = cc →
        typ.regularTolerance = δ → rstar ≤ typ.regularRadius →
        ∃ t₁ : ℕ, ∀ t : ℕ, t₁ ≤ t →
          (∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x +
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
      (Cm / (typ.regularRadius : ℝ) ^ (d - 6)) * (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)}) ∧
          (∀ x ∈ typMark t (0 : Vertex d), (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)} ≤
      Cp / (2 * (t : ℝ)) ^ 3) ∧
          (((typMark t (0 : Vertex d)).card : ℝ) ≤ Cb * (2 * (t : ℝ)) ^ (d - 1)))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (κ : Measure Bool) [IsProbabilityMeasure κ] (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (hedge : ∀ typ : TypicalParameters, typ.regularTolerance = δ → 1 ≤ typ.regularRadius →
      0 < typ.boundaryLower → 0 < typ.countLower → 0 ≤ typ.boundaryUpper →
      0 ≤ typ.countUpper → 0 ≤ typ.diameterUpper →
      ∃ k : ℕ, 0 < k ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ s : I,
        ((orParameter (criticalPoint d) s : I) : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∀ R : ℕ, ∃ A : Finset (Bond d),
          (∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A) ∧
          ∃ childNest : boxBonds (centeredBox 2 R) → centeredBox 2 R → SlabNest d →
              (∀ i, rsΩ d n A R i) → Option (SlabNest d),
            (∀ e z ℓ (x x' : ∀ i, rsΩ d n A R i), x (Sum.inr e) = x' (Sum.inr e) →
              x (Sum.inl z) = x' (Sum.inl z) → childNest e z ℓ x = childNest e z ℓ x') ∧
            (∀ e z ℓ (x : ∀ j, rsΩ d n A R j),
              κ {true} ≤ rsν d n A R (criticalPoint d) s (Sum.inr e)
                {y | (childNest e z ℓ (update x (Sum.inr e) y)).isSome = true}) ∧
            (∀ q e z ℓ ℓ',
              (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) →
              slabSiteOK d n A R typ z (rsΦ d n A R q) = true →
              (slabQ d n A R typ k (shiftedSlab d n) (typicalCube n (coarseShift (d := d) n (0 : Vertex 2)))) q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ →
              childNest e z ℓ (rsΦ d n A R q) = some ℓ' →
              (slabQ d n A R typ k (shiftedSlab d n) (typicalCube n (coarseShift (d := d) n (0 : Vertex 2)))) q z ℓ')) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  obtain ⟨typ, t₀, hr, htol, hbL, hcL, hbU, hcU, hdU, hpre⟩ :=
    pregood_of_moments_eta hd hA hc₀ hK hB0 hCarm hcross htail hBm hsize ordinary
      ha₁ ha₂ ha₃ hsum hc ha₁' ha₂' ha₃' hη hδ0 hmom
  obtain ⟨k, hk0, lam, hlam, n₁, hn₁⟩ := hedge typ htol hr hbL hcL hbU hcU hdU
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, n₂ = ⌈(k : ℝ) / typ.countLower⌉₊ := ⟨_, rfl⟩
  refine slab_upper_of_resampledNestInputs (by omega) hlam (max (max t₀ n₁) (max n₂ 1)) κ hθ0 hθ ?_
  intro n hn0 hn p hp
  have hnt : t₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn0
  have hnn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn0
  have hnn2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn0
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpge : (criticalPoint d : ℝ) ≤ (p : ℝ) := by
    rw [hp]
    have : 0 ≤ lam / (n : ℝ) ^ 2 := by positivity
    linarith
  obtain ⟨s, hs⟩ := exists_orParameter (criticalPoint d) p hpge hpc1
  refine ⟨s, hs, typicalCube n (coarseShift (d := d) n (0 : Vertex 2)), fun R => ?_⟩
  obtain ⟨A, hA', childNest, hloc, hpe, heQ⟩ := hn₁ n hnn1 s (by rw [hs]; exact hp) R
  have hk : (k : ℝ) ≤ typ.countLower * (2 * (n : ℝ)) ^ (d - 6) := by
    have h1 : (k : ℝ) / typ.countLower ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by rw [← hn₂]; exact_mod_cast hnn2)
    have h2 : (k : ℝ) ≤ (n : ℝ) * typ.countLower := (div_le_iff₀ hcL).mp h1
    have h3 : (n : ℝ) ≤ (2 * (n : ℝ)) ^ (d - 6) :=
      (by linarith : (n : ℝ) ≤ 2 * (n : ℝ)).trans
        (le_self_pow₀ (by linarith) (by omega))
    have h4 : typ.countLower * (n : ℝ) ≤ typ.countLower * (2 * (n : ℝ)) ^ (d - 6) :=
      mul_le_mul_of_nonneg_left h3 hcL.le
    linarith
  exact resampledSlabNestInputs_of_edge (by omega : 0 < n) s A typ k (shiftedSlab d n) _ κ hk hA'
    hκ (fun c => hpre n hnt c) childNest hloc hpe
    (slabQ d n A R typ k (shiftedSlab d n) (typicalCube n (coarseShift (d := d) n (0 : Vertex 2))))
    (fun q ℓ h => slabQ_root n A R typ k (by omega) _ q ℓ h) heQ
    (fun q v ℓ h => slabQ_join (by omega) (by omega) A R typ hk0 _ _ q v ℓ h)

end NearCritical
