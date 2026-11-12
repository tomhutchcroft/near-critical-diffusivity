module

public import NearCritical.Section10Survivor
public import NearCritical.MicroscopicChainPath

/-! Source `lem.nw.path`, logical core: a surviving chain carries a microscopic
chain.

The states of the chain carry clusters (`cl x`), each cluster has boundary
points (`bd c`). `Inv t x` is the invariant of the construction (in the
application: `x` is a nest of typical clusters of the cube at step `t`).

Hypotheses on one positive kernel step (the step succeeded and the new state is
an offspring):
* a step either keeps the clusters (a stay), or some cluster `rep` of the
  current state has, inside it, connections of length at most `A` between any
  two of its boundary points, and a bridge of length at most `B` from one of its
  boundary points to a boundary point of each cluster of the new state;
* at the exit step some cluster has a boundary point with an open exit edge.

`chainSurvives_geometry`: then, by backward induction over the remaining steps,
some cluster of the current state has `MicroscopicChainGeometry` from each of
its boundary points to the exit, with at most `m - 1` bridges.

No canonical order on clusters is used: the representative is any good cluster.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem chainSurvives_geometry {d : ℕ} {V X ι : Type*} (G : SimpleGraph V) (A B : ℝ)
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (z : Configuration d × Configuration d)
    (cl : X → Set ι) (bd : ℕ → ι → Set V) (Inv : ℕ → X → Prop) (Exit : V → Prop) (T : ℕ)
    (hexit : ∀ x y, Inv T x → 0 < k T x y z →
      ∃ rep ∈ cl x, ∃ v w, v ∈ bd T rep ∧ G.Adj v w ∧ Exit w ∧
        ∀ p ∈ bd T rep, ∃ C : SimpleGraph V, C ≤ G ∧ BoundedIntrinsicConnection C p v A)
    (hstep : ∀ t, t < T → ∀ x y, Inv t x → 0 < k t x y z →
      Inv (t+1) y ∧ ((cl y = cl x ∧ ∀ c ∈ cl x, bd t c ⊆ bd (t+1) c) ∨
        ∃ rep ∈ cl x,
          (∀ c' ∈ cl y, ∃ u ∈ bd t rep, ∃ v ∈ bd (t+1) c', ∃ D : SimpleGraph V, D ≤ G ∧
            BoundedIntrinsicConnection D u v B) ∧
          ∀ p ∈ bd t rep, ∀ u ∈ bd t rep, ∃ C : SimpleGraph V, C ≤ G ∧
            BoundedIntrinsicConnection C p u A)) :
    ∀ (m t : ℕ) (x : X), t + m = T + 1 → t ≤ T → Inv t x → ChainSurvives k m t x z →
      ∃ rep ∈ cl x, ∃ (n : ℕ) (y w : V), n + 1 ≤ m ∧ G.Adj y w ∧ Exit w ∧
        ∀ p ∈ bd t rep, MicroscopicChainGeometry G A B n p y := by
  intro m
  induction m with
  | zero =>
    intro t x h1 h2 _ _
    omega
  | succ m ih =>
    intro t x h1 h2 hInv hsurv
    obtain ⟨y, hk, hrest⟩ := hsurv
    by_cases hT : t = T
    · subst hT
      obtain ⟨rep, hrep, v, w, _, hadj, hw, hconn⟩ := hexit x y hInv hk
      refine ⟨rep, hrep, 0, v, w, by omega, hadj, hw, ?_⟩
      intro p hp
      exact hconn p hp
    · have htT : t < T := by omega
      obtain ⟨hInv', hcase⟩ := hstep t htT x y hInv hk
      obtain ⟨rep', hrep', n, yend, w, hn, hadj, hw, hgeo⟩ :=
        ih (t+1) y (by omega) (by omega) hInv' hrest
      rcases hcase with ⟨hstay, hbd⟩ | ⟨rep, hrep, hbridge, hinside⟩
      · have hrepx : rep' ∈ cl x := by rw [← hstay]; exact hrep'
        exact ⟨rep', hrepx, n, yend, w, by omega, hadj, hw,
          fun p hp => hgeo p (hbd rep' hrepx hp)⟩
      · obtain ⟨u, hu, v, hv, D, hDG, hD⟩ := hbridge rep' hrep'
        refine ⟨rep, hrep, n+1, yend, w, by omega, hadj, hw, ?_⟩
        intro p hp
        obtain ⟨C, hCG, hC⟩ := hinside p hp u hu
        exact ⟨C, D, u, v, hCG, hDG, hC, hD, hgeo v hv⟩

end NearCritical.Section10
