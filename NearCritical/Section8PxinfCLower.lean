module

public import NearCritical.Section8YSecondMoment
public import NearCritical.HeartBoundaryHitting

/-! The lower bound of source PxinfC (main.tex 3160–3170): `P[x ∈ fC] ≳ c₁^{d-4} n^{-3}`, via the
source's Cauchy–Schwarz step `P[Y>0] ≥ E[Y]²/E[Y²]` and the two moment bounds.

Radius form, `d = e+7`: `Q = centeredBox d R`, heart `H = centeredBox d s`, `|x|_∞ = R`,
`1 ≤ s`, `5s ≤ R`. The conclusion is
`κ·(s/R)^{d-4}/R³ ≤ P[x ∈ heartClusterUnion Q H]`, where `κ > 0` depends only on `e` and the
input constants and is chosen BEFORE `p, R, s, x`.

The assembly combines:
* `Y_firstmoment_of_box_lower`: `E[Y] ≥ c(s/R)^{d-1}`, given the box lower input `hbox`
  (lem.box_twopoint_lower at margin 1/2);
* `Y_secondmoment_of_inputs`: `E[Y²] ≤ C(2s+1)^{d+2}/R^{d-1}`, given the tree-graph and
  two-point inputs;
* `heartClusterUnion_probability_lower_boundary_second_moment` (existing).
All probabilistic inputs remain EXPLICIT hypotheses. This is not their discharge.
 -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open AppendixVariance Section8

theorem PxinfC_lower_of_inputs (e : ℕ) {c C0 C1 : ℝ} (hc : 0 < c) (hC0 : 0 ≤ C0)
    (hC1 : 0 ≤ C1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p : unitInterval) (R s : ℕ) (x : Vertex (e + 7))
      (tQ : Vertex (e + 7) → ℝ) (t : Vertex (e + 7) → Vertex (e + 7) → ℝ),
      1 ≤ s → 5 * s ≤ R → linfDist (0 : Vertex (e + 7)) x = R →
      (∀ u ∈ centeredBox (e + 7) R, 0 ≤ tQ u) →
      (∀ u ∈ centeredBox (e + 7) R, ∀ v, 0 ≤ t u v) →
      (∀ y ∈ boundarySites (centeredBox (e + 7) s), ∀ z ∈ boundarySites (centeredBox (e + 7) s),
        (percolation (e + 7) p).real
          (connectionToSetEvent ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) :
              Set (Vertex (e + 7))) x {y} ∩
            connectionToSetEvent ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) :
              Set (Vertex (e + 7))) x {z}) ≤
          ∑ u ∈ centeredBox (e + 7) R, tQ u * t u y * t u z) →
      (∀ u ∈ centeredBox (e + 7) R, tQ u ≤ C0 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) →
      (∀ u ∈ centeredBox (e + 7) R, ∀ v ∈ boundarySites (centeredBox (e + 7) s),
        t u v ≤ C1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (e + 5)) →
      (∀ y ∈ centeredBox (e + 7) R,
        R ≤ 2 * (R - linfDist (0 : Vertex (e + 7)) y) →
          c / (R : ℝ) ^ (e + 6) ≤ (percolation (e + 7) p).real
            (connectionToSetEvent ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) :
              Set (Vertex (e + 7))) x {y})) →
      κ * ((s : ℝ) / (R : ℝ)) ^ (e + 3) / (R : ℝ) ^ 3 ≤
        (percolation (e + 7) p).real
          {ω | x ∈ heartClusterUnion ω (centeredBox (e + 7) R) (centeredBox (e + 7) s)} := by
  obtain ⟨C, hC, hY2⟩ := Y_secondmoment_of_inputs e hC0 hC1
  refine ⟨c ^ 2 / ((C + 1) * 3 ^ (e + 9)), by positivity, ?_⟩
  intro p R s x tQ t hs h5s hxR htQ0 ht0 htree htQ ht hbox
  have hR : 1 ≤ R := by omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hxQ : x ∈ centeredBox (e + 7) R := by
    rw [← appendix_cube_eq_centeredBox, mem_cube_iff_dist_aux]; omega
  have hHQ : centeredBox (e + 7) s ⊆ centeredBox (e + 7) R := by
    intro y hy
    rw [mem_centeredBox] at hy ⊢
    intro i; have := hy i; constructor <;> omega
  have hxH : x ∉ centeredBox (e + 7) s := by
    intro hxs
    rw [← appendix_cube_eq_centeredBox, mem_cube_iff_dist_aux] at hxs
    omega
  -- first moment
  have hY1 := Y_firstmoment_of_box_lower (k := e + 6) (R := R) (s := s) p x hxQ (by omega) hR hc.le hbox
  set m1 : ℝ := c * ((s : ℝ) / (R : ℝ)) ^ (e + 6) with hm1
  have hm1pos : 0 < m1 := by rw [hm1]; positivity
  set EY := ∫ ω, heartConnectionCount (centeredBox (e + 7) R)
    (boundarySites (centeredBox (e + 7) s)) x ω ∂percolation (e + 7) p with hEY
  have hEYpos : 0 < EY := lt_of_lt_of_le hm1pos hY1
  -- second moment
  have hY2' := hY2 p R s x tQ t hR h5s hxR htQ0 ht0 htree htQ ht
  set EY2 := ∫ ω, (heartConnectionCount (centeredBox (e + 7) R)
    (boundarySites (centeredBox (e + 7) s)) x ω) ^ 2 ∂percolation (e + 7) p with hEY2
  have hEY2pos : 0 < EY2 := integral_heartConnectionCount_sq_pos p _ _ x hEYpos
  set M2 : ℝ := (C + 1) * (2 * (s : ℝ) + 1) ^ (e + 9) / (R : ℝ) ^ (e + 6) with hM2
  have hM2pos : 0 < M2 := by rw [hM2]; positivity
  have hEY2le : EY2 ≤ M2 := by
    refine hY2'.trans ?_
    rw [hM2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  -- Cauchy–Schwarz step
  have hCS := heartClusterUnion_probability_lower_boundary_second_moment p
    (centeredBox (e + 7) R) (centeredBox (e + 7) s) hHQ x hxQ hxH hEYpos
  have hratio : m1 ^ 2 / M2 ≤ EY ^ 2 / EY2 := by
    rw [div_le_div_iff₀ hM2pos hEY2pos]
    have h1 : m1 ^ 2 ≤ EY ^ 2 := pow_le_pow_left₀ hm1pos.le hY1 2
    exact mul_le_mul h1 hEY2le hEY2pos.le (by positivity)
  -- explicit order
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h3s : (2 * (s : ℝ) + 1) ^ (e + 9) ≤ (3 * (s : ℝ)) ^ (e + 9) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hC1' : (0 : ℝ) < C + 1 := by linarith
  have hK0 : (C + 1) * 3 ^ (e + 9) ≠ (0 : ℝ) := by positivity
  have hR0 : (R : ℝ) ≠ 0 := hRpos.ne'
  have hs0 : (s : ℝ) ≠ 0 := hspos.ne'
  have hM2' : M2 ≤ (C + 1) * (3 * (s : ℝ)) ^ (e + 9) / (R : ℝ) ^ (e + 6) := by
    rw [hM2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3s hC1'.le) (by positivity)
  have heq : c ^ 2 / ((C + 1) * 3 ^ (e + 9)) * ((s : ℝ) / (R : ℝ)) ^ (e + 3) / (R : ℝ) ^ 3 =
      m1 ^ 2 / ((C + 1) * (3 * (s : ℝ)) ^ (e + 9) / (R : ℝ) ^ (e + 6)) := by
    rw [hm1, div_eq_div_iff (by positivity) (by positivity)]
    rw [div_pow, div_pow, mul_pow]
    field_simp
    ring
  have hord : c ^ 2 / ((C + 1) * 3 ^ (e + 9)) * ((s : ℝ) / (R : ℝ)) ^ (e + 3) / (R : ℝ) ^ 3 ≤
      m1 ^ 2 / M2 := by
    rw [heq]
    exact div_le_div_of_nonneg_left (by positivity) hM2pos hM2'
  exact le_trans (le_trans hord hratio) hCS

end NearCritical
