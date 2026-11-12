module

public import NearCritical.HeartConnectionPairs
public import NearCritical.Section8YFirstMoment
public import NearCritical.AppendixSharpBubble
public import NearCritical.AppendixFRDSums
public import NearCritical.AppendixVarTerm1Phi

/-! Source lem.Y_secondmoment (main.tex 3196): `E[Y²] ≲ c₁^{d+2} n³`, here in radius form
`E[Y²] ≤ C·(2s+1)^{d+2}/R^{d-1}` (`d = e+7`, `Q = centeredBox d R`, `H = centeredBox d s`,
`∂H = {|y|_∞ = s}`, `|x|_∞ = R`, `5s ≤ R`). The constant `C` depends only on `e, C₀, C₁` and is
chosen BEFORE `p, R, s, x` (uniformity is visible in the statement).

`E[Y²] = ∑_{y,z∈∂H} P[x↔_Q y, x↔_Q z]` exactly (the existing `integral_heartConnectionCount_sq_pairs`).
EXPLICIT inputs (the probabilistic content):
* the tree-graph / BK branch-point bound `P[x↔y, x↔z] ≤ ∑_{u∈Q} τ_Q(x,u)τ(u,y)τ(u,z)`;
* the one-sided box bound `τ_Q(x,u) ≤ C₀(|x-u|+1)^{1-d}` [lem.box_twopoint_onesided];
* the full-space bound `τ(u,v) ≤ C₁(|u-v|+1)^{2-d}`.
Analytic proof, as in the source:
* split `u` at `|x-u| = R/2`;
* far part: `τ_Q(x,u) ≲ R^{1-d}` and the K-uniform `sharp_bubble`, giving `≲ R^{1-d}(|y-z|+1)^{4-d}`;
* near part: `|u-y| > 3R/10`, so `τ(u,y),τ(u,z) ≲ R^{2-d}`, and `ball_flat_sum` gives `≲ R^{5-2d}`,
  absorbed using `|y-z|+1 ≤ R`;
* pair sum: `boundary_maxr_pow_sum_le` (face projection, which avoids the source's per-shell count;
  that count fails at one shell) for `∑_z`, and the shell count `fiber_card_real_le` for `|∂H|`.
 -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open AppendixVariance Section8

lemma mem_cube_iff_dist_aux {D m : ℕ} {w : Fin D → ℤ} :
    w ∈ (cube m : Finset (Fin D → ℤ)) ↔ linfDist (0 : Fin D → ℤ) w ≤ m := by
  rw [cube_eq_linfBall, mem_linfBall_iff_dist 0 w (by positivity)]
  simp

lemma heart_eq_cubeBoundary (e s : ℕ) :
    boundarySites (centeredBox (e + 7) s) = (cubeBoundary s : Finset (Fin (e + 7) → ℤ)) := by
  ext y
  rw [centeredBox_boundary_norm_iff]
  simp only [cubeBoundary, Finset.mem_filter, mem_cube_iff_dist_aux]
  omega

lemma heart_eq_fiber (e s : ℕ) :
    boundarySites (centeredBox (e + 7) s) =
      (linfBall (0 : Fin (e + 7) → ℤ) (s : ℤ)).filter (fun u => linfDist 0 u = s) := by
  ext y
  rw [centeredBox_boundary_norm_iff, Finset.mem_filter,
    mem_linfBall_iff_dist 0 y (by positivity)]
  simp only [Int.toNat_natCast]
  omega

lemma centeredBox_dist_le {e R : ℕ} {u : Vertex (e + 7)} (hu : u ∈ centeredBox (e + 7) R) :
    linfDist (0 : Vertex (e + 7)) u ≤ R := by
  rw [← appendix_cube_eq_centeredBox] at hu
  exact mem_cube_iff_dist_aux.mp hu

/-- Source lem.Y_secondmoment from the explicit tree-graph and two-point inputs. -/
theorem Y_secondmoment_of_inputs (e : ℕ) {C0 C1 : ℝ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : unitInterval) (R s : ℕ) (x : Vertex (e + 7))
      (tQ : Vertex (e + 7) → ℝ) (t : Vertex (e + 7) → Vertex (e + 7) → ℝ),
      1 ≤ R → 5 * s ≤ R → linfDist (0 : Vertex (e + 7)) x = R →
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
      ∫ ω, (heartConnectionCount (centeredBox (e + 7) R)
          (boundarySites (centeredBox (e + 7) s)) x ω) ^ 2 ∂percolation (e + 7) p
        ≤ C * (2 * (s : ℝ) + 1) ^ (e + 9) / (R : ℝ) ^ (e + 6) := by
  set B : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set Cb : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
    (2 * 2 ^ (e + 5) + 3 ^ (e + 5) * (((((e + 3 : ℕ) : ℝ) + 1) /
      ((e + 3 : ℕ) : ℝ)) * 2 ^ (e + 3))) with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  set A : ℝ := C0 * 2 ^ (e + 6) * C1 ^ 2 * Cb + 2 * (C0 * C1 ^ 2 * 4 ^ (2 * e + 10) * B) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set Bnd : ℝ := (((e + 6 : ℕ) : ℝ) + 1) * (2 * (2 * ((e + 6 : ℕ) : ℝ) * 3 ^ (e + 5))) with hBnd
  have hBnd0 : 0 ≤ Bnd := by rw [hBnd]; positivity
  refine ⟨A * (2 * ((e + 7 : ℕ) : ℝ)) * Bnd, by positivity, ?_⟩
  intro p R s x tQ t hR h5s hxR htQ0 ht0 htree htQ ht
  set Q : Finset (Vertex (e + 7)) := centeredBox (e + 7) R with hQdef
  set H : Finset (Vertex (e + 7)) := boundarySites (centeredBox (e + 7) s) with hHdef
  have hNpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hN1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hxQ : x ∈ Q := by
    rw [hQdef, ← appendix_cube_eq_centeredBox, mem_cube_iff_dist_aux]; omega
  have hHs : ∀ y ∈ H, linfDist (0 : Vertex (e + 7)) y = s := fun y hy =>
    (centeredBox_boundary_norm_iff y).mp hy
  -- per-pair bound
  have hpair : ∀ y ∈ H, ∀ z ∈ H, ∑ u ∈ Q, tQ u * t u y * t u z ≤
      A / ((R : ℝ) ^ (e + 6) * ((linfDist y z + 1 : ℕ) : ℝ) ^ (e + 3)) := by
    intro y hy z hz
    have hys := hHs y hy
    have hzs := hHs z hz
    have hyz : linfDist y z + 1 ≤ R := by
      have h := linfDist_triangle y 0 z
      rw [linfDist_comm y 0] at h
      omega
    set D : ℝ := ((linfDist y z + 1 : ℕ) : ℝ) with hD
    have hD1 : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast (show 1 ≤ linfDist y z + 1 by omega)
    have hDR : D ≤ R := by rw [hD]; exact_mod_cast hyz
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun u => R ≤ 2 * linfDist x u)]
    -- far region
    have hfar : ∑ u ∈ Q.filter (fun u => R ≤ 2 * linfDist x u), tQ u * t u y * t u z ≤
        C0 * 2 ^ (e + 6) * C1 ^ 2 * Cb / ((R : ℝ) ^ (e + 6) * D ^ (e + 3)) := by
      have hpt : ∀ u ∈ Q.filter (fun u => R ≤ 2 * linfDist x u), tQ u * t u y * t u z ≤
          C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) * C1 ^ 2 *
            ((1 / ((linfDist y u + 1 : ℕ) : ℝ) ^ (e + 5)) *
              (1 / ((linfDist z u + 1 : ℕ) : ℝ) ^ (e + 5))) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huQ, hfr⟩ := hu
        have hinv := one_div_pow_le_of_le_mul_aux (a := (R : ℝ))
          (Q := ((linfDist x u + 1 : ℕ) : ℝ)) (c := 2) hNpos (by positivity) (by norm_num)
          (by exact_mod_cast (show R ≤ 2 * (linfDist x u + 1) by omega)) (e + 6)
        have hq : tQ u ≤ C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) :=
          (htQ u huQ).trans (by
            rw [div_eq_mul_one_div C0]; exact mul_le_mul_of_nonneg_left hinv hC0)
        have hty : t u y ≤ C1 * (1 / ((linfDist y u + 1 : ℕ) : ℝ) ^ (e + 5)) := by
          rw [linfDist_comm y u, ← div_eq_mul_one_div]; exact ht u huQ y hy
        have htz : t u z ≤ C1 * (1 / ((linfDist z u + 1 : ℕ) : ℝ) ^ (e + 5)) := by
          rw [linfDist_comm z u, ← div_eq_mul_one_div]; exact ht u huQ z hz
        have hb1 : 0 ≤ C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) := by positivity
        have hb2 : 0 ≤ C1 * (1 / ((linfDist y u + 1 : ℕ) : ℝ) ^ (e + 5)) := by positivity
        calc tQ u * t u y * t u z
            ≤ (C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6))) *
                (C1 * (1 / ((linfDist y u + 1 : ℕ) : ℝ) ^ (e + 5))) *
                (C1 * (1 / ((linfDist z u + 1 : ℕ) : ℝ) ^ (e + 5))) :=
              mul_le_mul (mul_le_mul hq hty (ht0 u huQ y) hb1) htz (ht0 u huQ z)
                (mul_nonneg hb1 hb2)
          _ = _ := by ring
      have hsub : Q.filter (fun u => R ≤ 2 * linfDist x u) ⊆ linfBall z ((2 * R : ℕ) : ℤ) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        have huR := centeredBox_dist_le hu.1
        rw [mem_linfBall_iff_dist z u (by positivity)]
        have h := linfDist_triangle z 0 u
        rw [linfDist_comm z 0] at h
        simp only [Int.toNat_natCast]
        omega
      have hbub := sharp_bubble y z (2 * R) _ hsub
      rw [← hCb] at hbub
      have hK0 : 0 ≤ C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) * C1 ^ 2 := by positivity
      calc _ ≤ ∑ u ∈ Q.filter (fun u => R ≤ 2 * linfDist x u),
            C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) * C1 ^ 2 *
              ((1 / ((linfDist y u + 1 : ℕ) : ℝ) ^ (e + 5)) *
                (1 / ((linfDist z u + 1 : ℕ) : ℝ) ^ (e + 5))) := Finset.sum_le_sum hpt
        _ = C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) * C1 ^ 2 *
            ∑ u ∈ Q.filter (fun u => R ≤ 2 * linfDist x u),
              ((1 / ((linfDist y u + 1 : ℕ) : ℝ) ^ (e + 5)) *
                (1 / ((linfDist z u + 1 : ℕ) : ℝ) ^ (e + 5))) := by rw [Finset.mul_sum]
        _ ≤ C0 * (2 ^ (e + 6) / (R : ℝ) ^ (e + 6)) * C1 ^ 2 * (Cb / D ^ (e + 3)) :=
            mul_le_mul_of_nonneg_left hbub hK0
        _ = _ := by ring
    -- near region
    have hnear : ∑ u ∈ Q.filter (fun u => ¬ R ≤ 2 * linfDist x u), tQ u * t u y * t u z ≤
        2 * (C0 * C1 ^ 2 * 4 ^ (2 * e + 10) * B) / ((R : ℝ) ^ (e + 6) * D ^ (e + 3)) := by
      have hpt : ∀ u ∈ Q.filter (fun u => ¬ R ≤ 2 * linfDist x u), tQ u * t u y * t u z ≤
          (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) ^ 2 * C0 *
            (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨huQ, hnr⟩ := hu
        have hfarv : ∀ v ∈ H, t u v ≤ C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5)) := by
          intro v hv
          have hvs := hHs v hv
          have h := linfDist_triangle (0 : Vertex (e + 7)) v x
          have h2 := linfDist_triangle v u x
          rw [linfDist_comm u x] at h2
          have hR4 : R ≤ 4 * (linfDist u v + 1) := by
            rw [linfDist_comm u v]; omega
          have hinv := one_div_pow_le_of_le_mul_aux (a := (R : ℝ))
            (Q := ((linfDist u v + 1 : ℕ) : ℝ)) (c := 4) hNpos (by positivity) (by norm_num)
            (by exact_mod_cast hR4) (e + 5)
          exact (ht u huQ v hv).trans (by
            rw [div_eq_mul_one_div C1]; exact mul_le_mul_of_nonneg_left hinv hC1)
        have hc : 0 ≤ C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5)) := by positivity
        have hq : tQ u ≤ C0 * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) := by
          rw [← div_eq_mul_one_div]; exact htQ u huQ
        calc tQ u * t u y * t u z
            ≤ (C0 * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6))) *
                (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) *
                (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) :=
              mul_le_mul (mul_le_mul hq (hfarv y hy) (ht0 u huQ y) (by positivity))
                (hfarv z hz) (ht0 u huQ z) (by positivity)
          _ = _ := by ring
      have hsub : Q.filter (fun u => ¬ R ≤ 2 * linfDist x u) ⊆ linfBall x (R : ℤ) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [mem_linfBall_iff_dist x u (by positivity)]
        simp only [Int.toNat_natCast]
        omega
      have hflat := ball_flat_sum x R
      have hK0 : 0 ≤ (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) ^ 2 * C0 := by positivity
      have hscale : (R + 1 : ℝ) / (R : ℝ) ^ (2 * e + 10) ≤
          2 / ((R : ℝ) ^ (e + 6) * D ^ (e + 3)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hDp : D ^ (e + 3) ≤ (R : ℝ) ^ (e + 3) := pow_le_pow_left₀ (by linarith) hDR _
        calc ((R : ℝ) + 1) * ((R : ℝ) ^ (e + 6) * D ^ (e + 3))
            ≤ (2 * (R : ℝ)) * ((R : ℝ) ^ (e + 6) * (R : ℝ) ^ (e + 3)) :=
              mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hDp (by positivity))
                (by positivity) (by positivity)
          _ = 2 * (R : ℝ) ^ (2 * e + 10) := by ring
      calc _ ≤ ∑ u ∈ Q.filter (fun u => ¬ R ≤ 2 * linfDist x u),
            (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) ^ 2 * C0 *
              (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) := Finset.sum_le_sum hpt
        _ = (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) ^ 2 * C0 *
            ∑ u ∈ Q.filter (fun u => ¬ R ≤ 2 * linfDist x u),
              (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) := by rw [Finset.mul_sum]
        _ ≤ (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) ^ 2 * C0 *
            ∑ u ∈ linfBall x (R : ℤ), (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hK0
        _ ≤ (C1 * (4 ^ (e + 5) / (R : ℝ) ^ (e + 5))) ^ 2 * C0 * (B * ((R : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (by rw [hB]; exact hflat) hK0
        _ = C0 * C1 ^ 2 * 4 ^ (2 * e + 10) * B * ((R + 1 : ℝ) / (R : ℝ) ^ (2 * e + 10)) := by
            ring
        _ ≤ C0 * C1 ^ 2 * 4 ^ (2 * e + 10) * B * (2 / ((R : ℝ) ^ (e + 6) * D ^ (e + 3))) :=
            mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = _ := by ring
    calc _ ≤ C0 * 2 ^ (e + 6) * C1 ^ 2 * Cb / ((R : ℝ) ^ (e + 6) * D ^ (e + 3)) +
          2 * (C0 * C1 ^ 2 * 4 ^ (2 * e + 10) * B) / ((R : ℝ) ^ (e + 6) * D ^ (e + 3)) :=
          add_le_add hfar hnear
      _ = _ := by rw [hA]; ring
  -- inner pair sum over H
  have hinner : ∀ y ∈ H, ∑ z ∈ H, (1 : ℝ) / ((linfDist y z + 1 : ℕ) : ℝ) ^ (e + 3) ≤
      Bnd * (2 * (s : ℝ) + 1) ^ 3 := by
    intro y hy
    have hyc : y ∈ (cube s : Finset (Fin (e + 6 + 1) → ℤ)) := by
      rw [mem_cube_iff_dist_aux]; exact le_of_eq (hHs y hy)
    have hb := boundary_maxr_pow_sum_le (k := e + 6) (by omega) (n := s) (r := 1) hyc
    rw [show e + 6 - 3 = e + 3 by omega, show e + 6 - 1 = e + 5 by omega] at hb
    have heq : ∑ z ∈ H, (1 : ℝ) / ((linfDist y z + 1 : ℕ) : ℝ) ^ (e + 3) =
        ∑ z ∈ (cubeBoundary s : Finset (Fin (e + 6 + 1) → ℤ)),
          (1 : ℝ) / (max ((1 : ℕ) : ℝ) ((linfDist y z + 1 : ℕ) : ℝ)) ^ (e + 3) := by
      rw [hHdef, heart_eq_cubeBoundary]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [max_eq_right (by exact_mod_cast (show 1 ≤ linfDist y z + 1 by omega))]
    rw [heq]
    refine hb.trans (le_of_eq ?_)
    rw [hBnd]; ring
  -- |H|
  have hHcard : ((H.card : ℕ) : ℝ) ≤ 2 * ((e + 7 : ℕ) : ℝ) * (2 * (s : ℝ) + 1) ^ (e + 6) := by
    have h := fiber_card_real_le (show 1 ≤ e + 7 by omega) (0 : Fin (e + 7) → ℤ)
      (K := s) (j := s) le_rfl
    rw [show e + 7 - 1 = e + 6 by omega] at h
    rw [hHdef, heart_eq_fiber]
    exact h
  -- assemble
  rw [integral_heartConnectionCount_sq_pairs p Q H x hxQ]
  have hstep : ∀ y ∈ H, ∑ z ∈ H, (percolation (e + 7) p).real
      (connectionToSetEvent (Q : Set (Vertex (e + 7))) x {y} ∩
        connectionToSetEvent (Q : Set (Vertex (e + 7))) x {z}) ≤
      A / (R : ℝ) ^ (e + 6) * (Bnd * (2 * (s : ℝ) + 1) ^ 3) := by
    intro y hy
    calc _ ≤ ∑ z ∈ H, A / (R : ℝ) ^ (e + 6) *
          ((1 : ℝ) / ((linfDist y z + 1 : ℕ) : ℝ) ^ (e + 3)) := by
          refine Finset.sum_le_sum (fun z hz => (htree y hy z hz).trans
            ((hpair y hy z hz).trans (le_of_eq ?_)))
          ring
      _ = A / (R : ℝ) ^ (e + 6) * ∑ z ∈ H, ((1 : ℝ) / ((linfDist y z + 1 : ℕ) : ℝ) ^ (e + 3)) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hinner y hy) (by positivity)
  calc _ ≤ ∑ y ∈ H, A / (R : ℝ) ^ (e + 6) * (Bnd * (2 * (s : ℝ) + 1) ^ 3) :=
        Finset.sum_le_sum hstep
    _ = ((H.card : ℕ) : ℝ) * (A / (R : ℝ) ^ (e + 6) * (Bnd * (2 * (s : ℝ) + 1) ^ 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * ((e + 7 : ℕ) : ℝ) * (2 * (s : ℝ) + 1) ^ (e + 6)) *
          (A / (R : ℝ) ^ (e + 6) * (Bnd * (2 * (s : ℝ) + 1) ^ 3)) :=
        mul_le_mul_of_nonneg_right hHcard (by positivity)
    _ = _ := by ring

end NearCritical
