module

public import NearCritical.HeartConnectionCount
public import NearCritical.Section8SourceAnnulusBridge

/-! Literal Section-8 consumer for source lem.Y_firstmoment (main.tex 3172).

Geometry, in the project's radius convention: `Q = centeredBox (k+1) R` (source `Λ_n`, with
`R = n/2`), the heart `H = centeredBox (k+1) s` (`s = c₁n/2`), and
`∂H = boundarySites H = {|y|_∞ = s}` (Astro's verified `centeredBox_boundary_norm_iff`).
`Y = heartConnectionCount Q ∂H x = ∑_{y∈∂H} 1(x ↔_Q y)`.

Derived here, all deterministic:
* `heart_face_card`: `|∂H| ≥ (2s+1)^{d-1}`, because the shell contains a full face. This is the
  source's `|∂H| ≥ c₂(c₁n)^{d-1}`.
* `heart_boundary_margin`: every `y ∈ ∂H` lies in `Q` with `l_y = R - |y| ≥ R/2` when `2s ≤ R`.
  This is the source's `l_y ≥ n/4`.
* `inner_face_far_from_ridges`: if every coordinate of `x` other than `i` satisfies
  `|x_j| < R/2`, then `x` is at distance `> R/2` from any point with two coordinates of size
  `R` (the ridge set `∂∂Q`). This is the source's distance `≥ n/4` from `x` to `∂∂Q`.

`Y_firstmoment_of_box_lower`: `E[Y] ≥ c·(s/R)^{d-1}` (source `c·c₁^{d-1}`), GIVEN the box lower
bound as an explicit input `hbox`: `c R^{1-d} ≤ P[x ↔_Q y]` for every `y ∈ Q` with margin
`R ≤ 2(R - |y|)`. The input is source lem.box_twopoint_lower at `α = 1/2`; its assembly is
proved in `AppendixBoxTwoPointLower`. This file is a CONSUMER and does
not discharge it. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open AppendixVariance Section8

/-- One full face of the radius-`s` shell. -/
def heartFace (k s : ℕ) : Finset (Vertex (k + 1)) :=
  Fintype.piFinset (fun i : Fin (k + 1) =>
    if i = 0 then ({(s : ℤ)} : Finset ℤ) else Finset.Icc (-(s : ℤ)) (s : ℤ))

lemma heartFace_card (k s : ℕ) : (heartFace k s).card = (2 * s + 1) ^ k := by
  unfold heartFace
  rw [Fintype.card_piFinset, Fin.prod_univ_succ]
  have hi : ∀ i : Fin k, (if i.succ = (0 : Fin (k + 1)) then ({(s : ℤ)} : Finset ℤ)
      else Finset.Icc (-(s : ℤ)) (s : ℤ)).card = 2 * s + 1 := by
    intro i
    rw [if_neg (Fin.succ_ne_zero i), Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl (fun i _ => hi i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, if_pos rfl, Finset.card_singleton, one_mul]

lemma heartFace_subset_boundary (k s : ℕ) :
    heartFace k s ⊆ boundarySites (centeredBox (k + 1) s) := by
  intro y hy
  unfold heartFace at hy
  rw [Fintype.mem_piFinset] at hy
  rw [centeredBox_boundary_norm_iff, linfDist_zero]
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    have h := hy i
    by_cases hi : i = 0
    · rw [if_pos hi, Finset.mem_singleton] at h
      show (y i).natAbs ≤ s
      omega
    · rw [if_neg hi, Finset.mem_Icc] at h
      show (y i).natAbs ≤ s
      omega
  · have h0 := hy 0
    rw [if_pos rfl, Finset.mem_singleton] at h0
    have hle : (y 0).natAbs ≤ Finset.univ.sup (fun i => (y i).natAbs) :=
      Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ 0)
    omega

/-- `|∂H| ≥ (2s+1)^{d-1}`. -/
theorem heart_face_card (k s : ℕ) :
    (2 * s + 1) ^ k ≤ (boundarySites (centeredBox (k + 1) s)).card := by
  rw [← heartFace_card k s]
  exact Finset.card_le_card (heartFace_subset_boundary k s)

/-- Every point of `∂H` lies in `Q` with margin `R - |y| ≥ R/2` (for `2s ≤ R`). -/
theorem heart_boundary_margin {k R s : ℕ} (h2s : 2 * s ≤ R) {y : Vertex (k + 1)}
    (hy : y ∈ boundarySites (centeredBox (k + 1) s)) :
    y ∈ centeredBox (k + 1) R ∧ R ≤ 2 * (R - linfDist (0 : Vertex (k + 1)) y) := by
  rw [centeredBox_boundary_norm_iff] at hy
  refine ⟨?_, by omega⟩
  rw [mem_centeredBox]
  intro i
  have hle : (y i).natAbs ≤ linfDist (0 : Vertex (k + 1)) y := by
    rw [linfDist_zero]
    exact Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i)
  omega

/-- A point whose coordinates off direction `i` are below `R/2` is at distance `> R/2` from every
point having two coordinates of absolute value `R` (the ridge set `∂∂Q`). -/
theorem inner_face_far_from_ridges {d R : ℕ} {x z : Vertex d} {i : Fin d}
    (hx : ∀ j, j ≠ i → 2 * (x j).natAbs < R) {j₁ j₂ : Fin d} (hj : j₁ ≠ j₂)
    (hz1 : (z j₁).natAbs = R) (hz2 : (z j₂).natAbs = R) :
    R < 2 * linfDist x z := by
  obtain ⟨j, hji, hzj⟩ : ∃ j, j ≠ i ∧ (z j).natAbs = R := by
    by_cases h : j₁ = i
    · exact ⟨j₂, fun h' => hj (h.trans h'.symm), hz2⟩
    · exact ⟨j₁, h, hz1⟩
  have hle : (x j - z j).natAbs ≤ linfDist x z := by
    unfold linfDist
    exact Finset.le_sup (f := fun i => (x i - z i).natAbs) (Finset.mem_univ j)
  have := hx j hji
  omega

/-- Source lem.Y_firstmoment, conditional on the box lower bound `hbox` at margin `1/2`. -/
theorem Y_firstmoment_of_box_lower {k R s : ℕ} (p : unitInterval) (x : Vertex (k + 1))
    (hxQ : x ∈ centeredBox (k + 1) R) (h2s : 2 * s ≤ R) (hR : 1 ≤ R) {c : ℝ} (hc : 0 ≤ c)
    (hbox : ∀ y ∈ centeredBox (k + 1) R,
      R ≤ 2 * (R - linfDist (0 : Vertex (k + 1)) y) →
        c / (R : ℝ) ^ k ≤ (percolation (k + 1) p).real
          (connectionToSetEvent ((centeredBox (k + 1) R : Finset (Vertex (k + 1))) :
            Set (Vertex (k + 1))) x {y})) :
    c * ((s : ℝ) / (R : ℝ)) ^ k ≤
      ∫ ω, heartConnectionCount (centeredBox (k + 1) R)
        (boundarySites (centeredBox (k + 1) s)) x ω ∂percolation (k + 1) p := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlow := integral_heartConnectionCount_lower p (centeredBox (k + 1) R)
    (boundarySites (centeredBox (k + 1) s)) x hxQ (a := c / (R : ℝ) ^ k)
    (fun y hy => hbox y (heart_boundary_margin h2s hy).1 (heart_boundary_margin h2s hy).2)
  have hcard : ((2 * s + 1 : ℕ) : ℝ) ^ k ≤
      ((boundarySites (centeredBox (k + 1) s)).card : ℝ) := by
    exact_mod_cast heart_face_card k s
  have ha0 : 0 ≤ c / (R : ℝ) ^ k := div_nonneg hc (by positivity)
  calc c * ((s : ℝ) / (R : ℝ)) ^ k = c / (R : ℝ) ^ k * (s : ℝ) ^ k := by
        rw [div_pow]; ring
    _ ≤ c / (R : ℝ) ^ k * ((2 * s + 1 : ℕ) : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by push_cast; linarith) k) ha0
    _ ≤ c / (R : ℝ) ^ k * ((boundarySites (centeredBox (k + 1) s)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard ha0
    _ ≤ _ := hlow

end NearCritical
