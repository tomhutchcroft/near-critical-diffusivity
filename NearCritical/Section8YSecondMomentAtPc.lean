module

public import NearCritical.Section8YSecondMoment
public import NearCritical.ThreePointTreeGraphDerivation
public import NearCritical.AppendixTwoPointBridge
public import NearCritical.HalfSpaceTranslation

/-! lem.Y_secondmoment at `p = p_c` with two of its three inputs DISCHARGED:
* the tree-graph / BK branch-point bound comes from the verified
  `restricted_tripod_connection_probability_le` (branch-point tripod and increasing BK in the
  finite domain `Q`), with `connectionToSetEvent_singleton_symm` for the order of the last factor;
* the full-space two-point bound for the restricted connection probabilities comes from
  assumption (A), via `twoPointBound_of_asymptotics` and `restricted_twoPointBound`.
The only remaining explicit input is the one-sided box bound
`P_pc[x ↔_Q u] ≤ C₀(|x-u|+1)^{1-d}` (lem.box_twopoint_onesided). The constant `C` depends only on
`e, C₀` and (A), and is chosen before `R, s, x`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open AppendixVariance Section8

theorem Y_secondmoment_at_pc (e : ℕ) (hA : TwoPointAsymptotics (e + 7)) {C0 : ℝ}
    (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R s : ℕ) (x : Vertex (e + 7)),
      1 ≤ R → 5 * s ≤ R → linfDist (0 : Vertex (e + 7)) x = R →
      (∀ u ∈ centeredBox (e + 7) R,
        (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) :
            Set (Vertex (e + 7))) x {u}) ≤ C0 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) →
      ∫ ω, (heartConnectionCount (centeredBox (e + 7) R)
          (boundarySites (centeredBox (e + 7) s)) x ω) ^ 2
          ∂percolation (e + 7) (criticalPoint (e + 7))
        ≤ C * (2 * (s : ℝ) + 1) ^ (e + 9) / (R : ℝ) ^ (e + 6) := by
  obtain ⟨C1, hC1, hTP⟩ := twoPointBound_of_asymptotics (d := e + 7) (by omega) hA
  obtain ⟨C, hC, H⟩ := Y_secondmoment_of_inputs e hC0 hC1.le
  refine ⟨C, hC, ?_⟩
  intro R s x hR h5s hxR htQ
  set D : Set (Vertex (e + 7)) :=
    ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) : Set (Vertex (e + 7))) with hD
  set P : Vertex (e + 7) → Vertex (e + 7) → ℝ := fun a b =>
    (percolation (e + 7) (criticalPoint (e + 7))).real (connectionToSetEvent D a {b}) with hP
  have hRB := restricted_twoPointBound hTP D
  refine H (criticalPoint (e + 7)) R s x (fun u => P x u) P hR h5s hxR
    (fun u _ => measureReal_nonneg) (fun u _ v => measureReal_nonneg) ?_ htQ ?_
  · intro y _ z _
    refine le_trans (restricted_tripod_connection_probability_le (criticalPoint (e + 7))
      (centeredBox (e + 7) R) x y z) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [hP, hD, connectionToSetEvent_singleton_symm
      (centeredBox (e + 7) R : Set (Vertex (e + 7))) z u]
  · intro u _ v _
    have h := (hRB u v).2
    rw [show e + 7 - 2 = e + 5 by omega] at h
    exact h

end NearCritical
