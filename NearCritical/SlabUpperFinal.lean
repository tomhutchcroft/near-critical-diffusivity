module

public import NearCritical.SlabUpperFromEdge
public import NearCritical.SlabEdgeInvariant
public import NearCritical.SlabConcreteChildNest

/-! **prop.slab.upper from cited inputs** (dimension `d >= 9`).

`slab_upper_final`: `p_c(Z^2 × {0..n}^(d-2)) - p_c <= C / n^2` for all `n >= 1`.

It instantiates the edge hypothesis of `slab_upper_of_edge` with the verified
concrete child rule: `slabChildNest_quantitative` (offspring failure bound in both
directions), `slabChildNest_pedge_of_failure_le`, `slabChildNest_local` and
`slabChildNest_edgeQ_shifted` (propagation of the invariant `slabQ`).

Order of choices: offspring tolerance `δ`; the typical parameters `typ` from the
pre-good theorem at tolerance `δ` and failure level `η`; `cSize` at radius
`typ.regularRadius`; the nest size `k`; the sprinkle constant `Lambda`; the
patch bounds `CB`, `KA`; the scale threshold. Ambient bonds: the internal bonds
of the box of radius `2nR + 2n` (`slabAmbient`), which contains every cube and
tube of the coarse box.

Hypotheses: assumption (A), the restricted rectangle lower bound, BKR, the split
crossing, far-face tail, boundary first moment, eq.cluster_size and one-arm
inputs of the pre-good theorem, the moment package at every tolerance,
`0 < p_c < 1`, and the cited planar mixed site-bond input for a law `κ` with
`κ{true} <= 1 - η`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set Function
open scoped Classical ENNReal
open Section10

variable {d : ℕ}

/-- Ambient bonds: internal bonds of a box containing all cubes and tubes. -/
def slabAmbient (d n R : ℕ) : Finset (Bond d) :=
  internalBondSet (centeredBox d (2 * n * R + 2 * n))

lemma coarseShift_abs_le {n R : ℕ} {v : Vertex 2} (hv : v ∈ centeredBox 2 R) (j : Fin d) :
    |coarseShift (d := d) n v j| ≤ 2 * (n : ℤ) * (R : ℤ) := by
  unfold coarseShift
  split_ifs with h
  · have hv' := mem_centeredBox.mp hv ⟨j.val, h⟩
    have hn : (0:ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    rw [abs_le]
    constructor <;> nlinarith [hv'.1, hv'.2]
  · simp
    positivity

lemma mem_ambientBox_of_close {n R : ℕ} {v : Vertex 2} (hv : v ∈ centeredBox 2 R)
    {x : Vertex d}
    (h : ∀ j, |((x j - coarseShift (d := d) n v j : ℤ) : ℝ)| < 2 * (n : ℝ)) :
    x ∈ centeredBox d (2 * n * R + 2 * n) := by
  rw [mem_centeredBox]
  intro j
  have h1 := abs_lt.mp (h j)
  have hc := abs_le.mp (coarseShift_abs_le (d := d) (n := n) hv j)
  have a1 : x j - coarseShift (d := d) n v j < 2 * (n : ℤ) := by
    have := h1.2
    exact_mod_cast this
  have a2 : -(2 * (n : ℤ)) < x j - coarseShift (d := d) n v j := by
    have := h1.1
    exact_mod_cast this
  have hM : ((2 * n * R + 2 * n : ℕ) : ℤ) = 2 * (n : ℤ) * (R : ℤ) + 2 * (n : ℤ) := by
    push_cast
    ring
  rw [hM]
  constructor <;> linarith [hc.1, hc.2]

lemma slabAmbient_cube (n R : ℕ) :
    ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ slabAmbient d n R := by
  intro v hv b hb
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmem : ∀ x : Vertex d, x ∈ slabCube n v → x ∈ centeredBox d (2 * n * R + 2 * n) :=
    fun x hx => mem_ambientBox_of_close hv fun j => by
      have := hx j
      linarith
  exact (mem_internalBondSet _ b).mpr ⟨hmem _ hb.1, hmem _ hb.2⟩

lemma slabAmbient_tube (n R : ℕ) :
    ∀ (e : boxBonds (centeredBox 2 R)) (b : Bond d),
      bondIn (slabTube n e.1.1 e.1.2) b → b ∈ slabAmbient d n R := by
  intro e b hb
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hv : e.1.1 ∈ centeredBox 2 R := ((mem_boxBonds _).1 e.2).1
  have hmem : ∀ x : Vertex d, x ∈ slabTube n e.1.1 e.1.2 →
      x ∈ centeredBox d (2 * n * R + 2 * n) :=
    fun x hx => mem_ambientBox_of_close hv fun j => by
      by_cases hj : j.val = e.1.2.val
      · have := hx.1 j hj
        rw [abs_lt]
        constructor <;> linarith [this.1, this.2]
      · have := hx.2 j hj
        linarith
  exact (mem_internalBondSet _ b).mpr ⟨hmem _ hb.1, hmem _ hb.2⟩

set_option maxHeartbeats 1600000 in
theorem slab_upper_final {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1)
    (hc : 0 < c) (ha₁' : 0 < a₁) (ha₂' : 0 < a₂) (ha₃' : 0 < a₃)
    (rectangle : RestrictedRectangleLowerInput d) (reimer : FiniteBernoulliBKRInput)
    (hp0 : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    {η : ℝ} (hη : 0 < η)
    (hmomAll : ∀ δ : ℝ, 0 < δ → ∃ cc : ℝ, 0 < cc ∧ cc ≤ 1 / 16 ∧ ∃ Cm Cp Cb : ℝ, 0 ≤ Cm ∧ 0 ≤ Cp ∧ 0 ≤ Cb ∧
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
    (κ : Measure Bool) [IsProbabilityMeasure κ] (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθ : MixedSiteBondPercolationInput 2 κ θ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨δ, hδ, hq⟩ := slabChildNest_quantitative hd hA rectangle reimer
  refine slab_upper_of_edge hd hA hc₀ hK hB0 hCarm hcross htail hBm hsize ordinary
    ha₁ ha₂ ha₃ hsum hc ha₁' ha₂' ha₃' hη hδ (hmomAll δ hδ) hpc1 κ hκ hθ0 hθ ?_
  intro typ htol hr hbL hcL hbU hcU hdU
  obtain ⟨cSize, hcS, hk⟩ := hq typ.regularRadius hr η hη
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌈cSize / (4 * typ.boundaryLower)⌉₊ +
      ⌈cSize / (16 * typ.countLower * typ.boundaryLower ^ 2)⌉₊ + 1 := ⟨_, rfl⟩
  have hk0 : 0 < k := by omega
  have hk1 : cSize / (4 * typ.boundaryLower) ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈cSize / (4 * typ.boundaryLower)⌉₊ ≤ k by omega))
  have hk2 : cSize / (16 * typ.countLower * typ.boundaryLower ^ 2) ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈cSize / (16 * typ.countLower * typ.boundaryLower ^ 2)⌉₊ ≤ k by omega))
  have hS : cSize ≤ 4 * (k : ℝ) * typ.boundaryLower := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * typ.boundaryLower)).mp hk1
    calc cSize ≤ (k : ℝ) * (4 * typ.boundaryLower) := h
      _ = _ := by ring
  have hST : cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2 := by
    have h := (div_le_iff₀
      (by positivity : (0:ℝ) < 16 * typ.countLower * typ.boundaryLower ^ 2)).mp hk2
    calc cSize ≤ (k : ℝ) * (16 * typ.countLower * typ.boundaryLower ^ 2) := h
      _ = _ := by ring
  obtain ⟨Lambda, hL, hCK⟩ := hk k hk0
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk0
  obtain ⟨N₀, hN₀, hfail⟩ := hCK (8 * typ.boundaryUpper + 1) (4 * (k : ℝ) * typ.boundaryUpper + 1)
    (by positivity) (by positivity)
  obtain ⟨nT, hnT⟩ : ∃ nT : ℕ,
      nT = ⌈cSize / (4 * typ.countLower * typ.boundaryLower)⌉₊ := ⟨_, rfl⟩
  refine ⟨k, hk0, Lambda, hL, max N₀ (max nT 1), ?_⟩
  intro n hn s hs R
  have hnN : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnT' : nT ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hT : cSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (n : ℝ)) ^ (d - 6) := by
    have h1 : cSize / (4 * typ.countLower * typ.boundaryLower) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by rw [← hnT]; exact_mod_cast hnT')
    have h2 := (div_le_iff₀
      (by positivity : (0:ℝ) < 4 * typ.countLower * typ.boundaryLower)).mp h1
    have h3 : (n : ℝ) ≤ (2 * (n : ℝ)) ^ (d - 6) :=
      (by linarith : (n : ℝ) ≤ 2 * (n : ℝ)).trans (le_self_pow₀ (by linarith) (by omega))
    have h4 : (4 * typ.countLower * typ.boundaryLower) * (n : ℝ) ≤
        (4 * typ.countLower * typ.boundaryLower) * (2 * (n : ℝ)) ^ (d - 6) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hsn : Lambda ≤ (s : ℝ) * (n : ℝ) ^ 2 := by
    have hs' : (criticalPoint d : ℝ) + (1 - (criticalPoint d : ℝ)) * (s : ℝ) =
        (criticalPoint d : ℝ) + Lambda / (n : ℝ) ^ 2 := hs
    have h1 : Lambda / (n : ℝ) ^ 2 = (1 - (criticalPoint d : ℝ)) * (s : ℝ) := by linarith
    have h2 : (1 - (criticalPoint d : ℝ)) * (s : ℝ) ≤ (s : ℝ) := by
      nlinarith [mul_nonneg hp0.le s.2.1]
    have h3 : Lambda / (n : ℝ) ^ 2 ≤ (s : ℝ) := by linarith
    exact (div_le_iff₀ (by positivity)).mp h3
  refine ⟨slabAmbient d n R, slabAmbient_cube n R,
    slabChildNest hd2 n R (slabAmbient d n R) typ k hk0 typ.regularRadius δ cSize
      (8 * typ.boundaryUpper + 1) (4 * (k : ℝ) * typ.boundaryUpper + 1), ?_, ?_, ?_⟩
  · intro e z ℓ x x' he hz
    exact slabChildNest_local hd2 n R _ typ k hk0 _ δ cSize _ _ e z ℓ x x' he hz
  · exact slabChildNest_pedge_of_failure_le hd2 n R _ typ k hk0 _ δ cSize _ _ s κ hκ
      (hfail n hnN s hsn R _ (slabAmbient_tube n R) typ)
  · exact slabChildNest_edgeQ_shifted (by omega) hd2 (by omega) hp0 hpc1 R _ typ k hk0 _
      (slabAmbient_cube n R) (slabAmbient_tube n R) hbL.le hcL.le (le_of_eq htol)
      (by linarith) (by linarith) hS hT hST

end NearCritical
