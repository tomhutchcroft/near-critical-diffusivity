module

public import NearCritical.SlabUpperNestInputs
public import NearCritical.HalfSpaceTranslation

/-! The slab upper bound in the SHIFTED slab.

The slab `slabVertices d 2 n` is `0 <= x_j <= n` for `j >= 2`, whereas the cubes
and tubes of `SlabUpperBlockGeometry` are centred at `0` in those coordinates.
The source works "up to a translation" (main.tex 6082). This file makes that
explicit.

* `restrictedReachFar_translate`: translation invariance of the percolation law
  gives `P[reachFar S F N] <= P[reachFar (a + S) (a + F) M]` if
  `M + |a| <= N`.
* `shiftedSlab d n`: `-(n/2) <= x_j <= n - n/2` for `j >= 2`, the slab translated
  by `-(n/2)` in the transverse coordinates; `slabCube_subset_shiftedSlab`,
  `slabTube_subset_shiftedSlab`: all cubes and tubes lie in it.
* `slab_upper_of_nestInputs_shifted`: prop.slab.upper for `slabVertices d 2 n`
  from nest-rule inputs stated in the shifted slab.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Function
open scoped ENNReal Classical

variable {d : ℕ}

lemma vertexSize_le_add (a y : Vertex d) : vertexSize y ≤ vertexSize (a + y) + vertexSize a := by
  unfold vertexSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Pi.add_apply]
  omega

theorem restrictedReachFar_translate (p : I) (a : Vertex d) (S : Set (Vertex d))
    (F : Finset (Vertex d)) {N M : ℕ} (hNM : M + vertexSize a ≤ N) :
    percolation d p (restrictedReachFarEvent S F N) ≤
      percolation d p (restrictedReachFarEvent ((fun z => a + z) '' S)
        (F.image (fun z => a + z)) M) := by
  have hsub : translateConfiguration a ⁻¹' restrictedReachFarEvent S F N ⊆
      restrictedReachFarEvent ((fun z => a + z) '' S) (F.image (fun z => a + z)) M := by
    rintro ω ⟨x, hx, y, hy, hr⟩
    refine ⟨a + x, Finset.mem_image_of_mem _ hx, a + y, ?_,
      hr.map (restrictedTranslationGraphIso a ω S).toHom⟩
    have := vertexSize_le_add a y
    omega
  calc percolation d p (restrictedReachFarEvent S F N)
      = ((percolation d p).map (translateConfiguration a)) (restrictedReachFarEvent S F N) := by
        rw [percolation_map_translation]
    _ = percolation d p (translateConfiguration a ⁻¹' restrictedReachFarEvent S F N) :=
        Measure.map_apply (measurable_translateConfiguration a)
          (measurableSet_restrictedReachFarEvent S F N)
    _ ≤ _ := measure_mono hsub

/-- The slab translated by `-(n/2)` in the transverse coordinates. -/
def shiftedSlab (d n : ℕ) : Set (Vertex d) :=
  {x | ∀ j : Fin d, 2 ≤ j.val → -((n / 2 : ℕ) : ℤ) ≤ x j ∧ x j ≤ (n : ℤ) - ((n / 2 : ℕ) : ℤ)}

/-- The transverse shift. -/
def slabShift (d n : ℕ) : Vertex d := fun j => if j.val < 2 then 0 else ((n / 2 : ℕ) : ℤ)

lemma slabShift_image (d n : ℕ) :
    (fun z => slabShift d n + z) '' shiftedSlab d n = slabVertices d 2 n := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩ j hj
    have h := hw j hj
    have hs : slabShift d n j = ((n / 2 : ℕ) : ℤ) := by
      unfold slabShift
      rw [if_neg (by omega)]
    change 0 ≤ slabShift d n j + w j ∧ slabShift d n j + w j ≤ (n : ℤ)
    rw [hs]
    constructor <;> omega
  · intro hx
    refine ⟨-slabShift d n + x, fun j hj => ?_, add_neg_cancel_left _ _⟩
    have h := hx j hj
    have hs : slabShift d n j = ((n / 2 : ℕ) : ℤ) := by
      unfold slabShift
      rw [if_neg (by omega)]
    rw [Pi.add_apply, Pi.neg_apply, hs]
    constructor <;> omega

lemma coarseShift_transverse (n : ℕ) (v : Vertex 2) (j : Fin d) (hj : 2 ≤ j.val) :
    coarseShift (d := d) n v j = 0 := by
  unfold coarseShift
  rw [dif_neg (by omega)]

lemma mem_shiftedSlab_of_abs_lt {n : ℕ} {x : Vertex d}
    (h : ∀ j : Fin d, 2 ≤ j.val → |((x j : ℤ) : ℝ)| < (n : ℝ) / 2) : x ∈ shiftedSlab d n := by
  intro j hj
  have h1 := abs_lt.mp (h j hj)
  have h2 : (-(n : ℤ) : ℝ) < ((2 * x j : ℤ) : ℝ) := by push_cast; linarith [h1.1]
  have h3 : ((2 * x j : ℤ) : ℝ) < ((n : ℤ) : ℝ) := by push_cast; linarith [h1.2]
  have h2' : -(n : ℤ) < 2 * x j := by exact_mod_cast h2
  have h3' : 2 * x j < (n : ℤ) := by exact_mod_cast h3
  constructor <;> omega

theorem slabCube_subset_shiftedSlab (n : ℕ) (v : Vertex 2) :
    slabCube (d := d) n v ⊆ shiftedSlab d n := by
  intro x hx
  refine mem_shiftedSlab_of_abs_lt fun j hj => ?_
  have h := hx j
  rw [coarseShift_transverse n v j hj, sub_zero] at h
  exact h

theorem slabTube_subset_shiftedSlab (n : ℕ) (u : Vertex 2) (i : Fin 2) :
    slabTube (d := d) n u i ⊆ shiftedSlab d n := by
  intro x hx
  refine mem_shiftedSlab_of_abs_lt fun j hj => ?_
  have h := hx.2 j (by have := i.2; omega)
  rw [coarseShift_transverse n u j hj, sub_zero] at h
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- prop.slab.upper from nest-rule inputs in the shifted slab. -/
theorem slab_upper_of_nestInputs_shifted (hd : 2 ≤ d) {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞} (hθ0 : θ ≠ 0)
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : I,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ s : I, orParameter (criticalPoint d) s = p ∧ ∃ F : Finset (Vertex d),
          ∀ R, Nonempty (SlabNestInputs d n R (criticalPoint d) s (shiftedSlab d n) F κ)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  refine slab_upper_inverse_square_of_reachFar hlam n₀ ?_
  intro n hn0 hn p hp
  obtain ⟨s, hsp, F, hX⟩ := hmodel n hn0 hn p hp
  refine ⟨F.image (fun z => slabShift d n + z), θ, hθ0, fun N => ?_⟩
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, N' = N + vertexSize (slabShift d n) := ⟨_, rfl⟩
  have h := (hX N').some.reachFar_ge hd (by omega) hθ
  rw [hsp] at h
  have h1 := h.trans (measure_mono
    (restrictedReachFarEvent_antitone _ F (le_two_mul_sub N' n hn)))
  have h2 := restrictedReachFar_translate p (slabShift d n) (shiftedSlab d n) F
    (N := N') (M := N) (by omega)
  rw [slabShift_image] at h2
  exact h1.trans h2

end NearCritical
