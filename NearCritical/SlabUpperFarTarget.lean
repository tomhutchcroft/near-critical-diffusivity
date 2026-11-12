module

public import NearCritical.SlabUpperSlabBlocks
public import NearCritical.SlabUpperNestInvariant
public import NearCritical.LatticeDomain

/-! Nest semantics `good` of prop.slab.upper reduced to the source's ONE-STEP
connection facts on the literal coarse box `centeredBox 2 R`.

`slabNestJoined n S F ω v`: some point of the cube `slabCube n v` is joined to the
root set `F` inside the slab `S` in configuration `ω` (the source "the k-nest of
`v` is connected to the root nest"). If the root move and each successful tube
move preserve this (source: "each added k-nest is connected to a single cluster
of the k-nest from which it was added"), then a nonzero payoff reaches a cube of
the inner boundary of the coarse box, and every point of such a cube has
`vertexSize ≥ 2nR - n`. This is DERIVED here (deterministic geometry), so the
reach-far event at scale `N = 2nR - n` follows. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval
open scoped ENNReal Classical

variable {d : ℕ}

/-- An inner-boundary site of `centeredBox 2 R` has a coordinate of size `≥ R`. -/
theorem exists_coord_abs_ge_of_innerBoundary {R : ℕ} {v : Vertex 2}
    (hv : v ∈ centeredBox 2 R) {y : Vertex 2} (hy : y ∉ centeredBox 2 R)
    (hadj : (openGraph (fun _ => true : Configuration 2)).Adj v y) :
    ∃ c : Fin 2, (R : ℤ) ≤ |v c| := by
  rw [mem_centeredBox] at hv hy
  push Not at hy
  obtain ⟨c, hc⟩ := hy
  obtain ⟨e, -, h | h⟩ := hadj
  · obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    have hb : bondTip e e.2 = e.1 e.2 + 1 := by simp [bondTip]
    by_cases hce : c = e.2
    · subst hce
      rw [hb] at hc
      have := hv e.2
      refine ⟨e.2, le_abs.2 (Or.inl ?_)⟩
      have := hc (by omega)
      omega
    · have hb' : bondTip e c = e.1 c := by simp [bondTip, Function.update_of_ne hce]
      rw [hb'] at hc
      have := hv c
      have := hc (by omega)
      omega
  · obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    have hb : bondTip e e.2 = e.1 e.2 + 1 := by simp [bondTip]
    by_cases hce : c = e.2
    · subst hce
      have hvc := hv e.2
      rw [hb] at hvc
      refine ⟨e.2, ?_⟩
      rw [hb]
      refine le_abs.2 (Or.inr ?_)
      by_contra hlt
      have := hc (by omega)
      omega
    · have hb' : bondTip e c = e.1 c := by simp [bondTip, Function.update_of_ne hce]
      have hvc := hv c
      rw [hb'] at hvc
      have := hc (by omega)
      omega

/-- Every point of the cube of a coarse site with a coordinate of size `≥ R` is at
`vertexSize ≥ 2nR - n`. -/
theorem vertexSize_ge_of_mem_slabCube (hd : 2 ≤ d) {n R : ℕ} {v : Vertex 2} {c : Fin 2}
    (hc : (R : ℤ) ≤ |v c|) {w : Vertex d} (hw : w ∈ slabCube n v) :
    2 * n * R - n ≤ vertexSize w := by
  have h1 := hw (Fin.castLE hd c)
  rw [coarseShift_apply hd] at h1
  set a : ℤ := w (Fin.castLE hd c) with ha
  have h2 : |a - 2 * (n : ℤ) * v c| * 2 < (n : ℤ) := by
    have h3 : |((a - 2 * (n : ℤ) * v c : ℤ) : ℝ)| * 2 < (n : ℝ) := by linarith
    have h4 : ((|a - 2 * (n : ℤ) * v c| * 2 : ℤ) : ℝ) < ((n : ℤ) : ℝ) := by
      rw [Int.cast_mul, Int.cast_abs, Int.cast_natCast]
      first
        | exact h3
        | (rw [Int.cast_ofNat]; exact h3)
        | simpa using h3
    exact Int.cast_lt.mp h4
  have h5 : |2 * (n : ℤ) * v c| = 2 * (n : ℤ) * |v c| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * (n : ℤ))]
  have h6 : |2 * (n : ℤ) * v c| - |a| ≤ |a - 2 * (n : ℤ) * v c| := by
    rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
  have h7 : 2 * (n : ℤ) * (R : ℤ) ≤ 2 * (n : ℤ) * |v c| :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have h8 : ((2 * n * R : ℕ) : ℤ) ≤ ((a.natAbs + n : ℕ) : ℤ) := by
    push_cast
    first
      | linarith
      | (rw [Int.natCast_natAbs]; linarith)
  have h9 : 2 * n * R ≤ a.natAbs + n := by exact_mod_cast h8
  have h10 : a.natAbs ≤ vertexSize w := by
    unfold vertexSize
    exact Finset.single_le_sum (f := fun i => (w i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Fin.castLE hd c))
  omega

/-- Source k-nest connection: some point of the cube of `v` is joined to `F` in `S`. -/
def slabNestJoined (n : ℕ) (S : Set (Vertex d)) (F : Finset (Vertex d))
    (ω : Configuration d) (v : Vertex 2) : Prop :=
  ∃ x ∈ F, ∃ w ∈ slabCube n v, (restrictedGraph ω S).Reachable x w

/-- The `good` field from one-step nest connection facts on `centeredBox 2 R`. -/
theorem slab_good_of_oneStep (hd : 2 ≤ d) {n R : ℕ} (S : Set (Vertex d))
    (F : Finset (Vertex d)) (A : Finset (Bond d)) (h0 : (0 : Vertex 2) ∈ centeredBox 2 R)
    (succ : ExploreState (centeredBox 2 R) (boxBonds (centeredBox 2 R)) →
      (∀ i, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i → Bool) → Bool)
    (ω : Bond d × Bool → Bool)
    (hroot : ∀ st, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st →
      exploreMove (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st = some .root →
      succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
      slabNestJoined n S F (sprinkleConfiguration ω) 0)
    (hedge : ∀ st e z, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st →
      (∀ v ∈ st.A, slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2)) →
      exploreMove (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st =
        some (.edge e z) →
      succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
      slabNestJoined n S F (sprinkleConfiguration ω) (z : Vertex 2)) :
    explorePayoff (boxInnerBoundary (centeredBox 2 R))
      (adaptiveRun (exploreQuery (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R))
        (exploreNext (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R)) succ
        (Fintype.card (centeredBox 2 R ⊕ boxBonds (centeredBox 2 R))) ⟨∅, ∅, ∅, ∅, ∅⟩
        (blockFamily (slabSprinkleBlocks (d := d) n A (centeredBox 2 R)) ω)) ≠ 0 →
      sprinkleConfiguration ω ∈ restrictedReachFarEvent S F (2 * n * R - n) := by
  intro h
  obtain ⟨v, hv, x, hx, w, hw, hr⟩ :=
    explorePayoff_ne_zero_good (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R)
      (boxInnerBoundary (centeredBox 2 R)) succ
      (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω)
      (fun v : centeredBox 2 R => slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2))
      hroot hedge h
  refine ⟨x, hx, w, ?_, hr⟩
  simp only [boxInnerBoundary, Finset.mem_filter] at hv
  obtain ⟨y, hy, hadj⟩ := hv.2
  obtain ⟨c, hc⟩ := exists_coord_abs_ge_of_innerBoundary v.2 hy hadj
  exact vertexSize_ge_of_mem_slabCube hd hc hw

end NearCritical
