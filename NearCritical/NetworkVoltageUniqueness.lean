module

public import NearCritical.NetworkMaximumPrinciple

/-! Uniqueness on boundary-connected components. A degenerate Dirichlet problem
may have nonunique values on components not meeting the boundary, but its open
edge gradients and its boundary-connected vertex values are unique. -/
@[expose] public section
namespace NearCritical.Network
open Set Finset
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

/-- Equal Dirichlet values make the difference an admissible test function for
both harmonic equations. Its weighted energy is therefore zero. -/
theorem IsHarmonic.energy_sub_eq_zero {a : E → ℝ} {boundary : Set V} {u v : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (hv : G.IsHarmonic a boundary v)
    (hboundary : ∀ z ∈ boundary, u z = v z) : G.energy a (u - v) = 0 := by
  have hw : ∀ z ∈ boundary, (u - v) z = 0 := by
    intro z hz
    simp [hboundary z hz]
  have h1 := hu (u - v) hw
  have h2 := hv (u - v) hw
  have heq : G.energy a (u - v) = G.pairing a (u - v) u - G.pairing a (u - v) v := by
    simp only [energy, pairing, gradient, Pi.sub_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq, h1, h2, sub_self]

/-- Open-edge gradients do not depend on the choice of harmonic extension. -/
theorem IsHarmonic.gradient_eq_of_boundary_eq {a : E → ℝ} {boundary : Set V} {u v : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (hv : G.IsHarmonic a boundary v)
    (ha : ∀ e, 0 ≤ a e) (hboundary : ∀ z ∈ boundary, u z = v z)
    (e : E) (he : 0 < a e) : G.gradient u e = G.gradient v e := by
  have hzero := hu.energy_sub_eq_zero G hv hboundary
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ mul_nonneg (ha j) (sq_nonneg (G.gradient (u - v) j)))).mp hzero e (Finset.mem_univ e)
  have hsq : (G.gradient (u - v) e) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt he)
  have hdiff := sq_eq_zero_iff.mp hsq
  dsimp only [gradient, Pi.sub_apply] at hdiff ⊢
  linarith

/-- On a component meeting the boundary, harmonic extensions agree pointwise.
Closed-edge voltage drops are consequently unique whenever both endpoints are
boundary-connected, without fixing values on all other components. -/
theorem IsHarmonic.eq_of_reachable_boundary {a : E → ℝ} {boundary : Set V} {u v : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (hv : G.IsHarmonic a boundary v)
    (ha : ∀ e, 0 ≤ a e) (hboundary : ∀ z ∈ boundary, u z = v z)
    {x z : V} (hpath : (G.positiveGraph a Set.univ).Reachable x z) (hz : z ∈ boundary) :
    u x = v x := by
  have hstep {p q : V} (hpq : (G.positiveGraph a Set.univ).Adj p q) :
      u q - v q = u p - v p := by
    obtain ⟨_, _, _, e, he, h | h⟩ := hpq
    · obtain ⟨rfl, rfl⟩ := h
      have hgrad := hu.gradient_eq_of_boundary_eq G hv ha hboundary e he
      dsimp only [gradient] at hgrad
      linarith
    · obtain ⟨rfl, rfl⟩ := h
      have hgrad := hu.gradient_eq_of_boundary_eq G hv ha hboundary e he
      dsimp only [gradient] at hgrad
      linarith
  have hdiff : u z - v z = u x - v x := by
    clear hz
    rw [SimpleGraph.reachable_iff_reflTransGen] at hpath
    induction hpath with
    | refl => rfl
    | tail _ h ih => exact (hstep h).trans ih
  have hb := hboundary z hz
  linarith

/-- Version with the boundary-access witness packaged existentially. -/
theorem IsHarmonic.eq_of_boundary_access {a : E → ℝ} {boundary : Set V} {u v : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (hv : G.IsHarmonic a boundary v)
    (ha : ∀ e, 0 ≤ a e) (hboundary : ∀ z ∈ boundary, u z = v z) {x : V}
    (hx : ∃ z ∈ boundary, (G.positiveGraph a Set.univ).Reachable x z) : u x = v x := by
  obtain ⟨z, hz, hpath⟩ := hx
  exact hu.eq_of_reachable_boundary G hv ha hboundary hpath hz

/-- Energy minimizers with the same data have identical gradients on every
positive-weight edge. Existence and global pointwise uniqueness are not assumed. -/
theorem IsMinimizer.gradient_eq_of_same_data {a : E → ℝ} {boundary : Set V}
    {data u v : V → ℝ} (hu : G.IsMinimizer a boundary data u)
    (hv : G.IsMinimizer a boundary data v) (ha : ∀ e, 0 ≤ a e) (e : E) (he : 0 < a e) :
    G.gradient u e = G.gradient v e := by
  exact (hu.isHarmonic G).gradient_eq_of_boundary_eq G (hv.isHarmonic G) ha
    (fun z hz ↦ (hu.1 z hz).trans (hv.1 z hz).symm) e he

/-- A source-prescribed minimizer and any selected minimizer coincide on every
boundary-connected vertex; arbitrary boundary-free constants have no effect. -/
theorem IsMinimizer.eq_of_boundary_access {a : E → ℝ} {boundary : Set V}
    {data u v : V → ℝ} (hu : G.IsMinimizer a boundary data u)
    (hv : G.IsMinimizer a boundary data v) (ha : ∀ e, 0 ≤ a e) {x : V}
    (hx : ∃ z ∈ boundary, (G.positiveGraph a Set.univ).Reachable x z) : u x = v x := by
  exact (hu.isHarmonic G).eq_of_boundary_access G (hv.isHarmonic G) ha
    (fun z hz ↦ (hu.1 z hz).trans (hv.1 z hz).symm) hx

/-- In particular, the voltage across a possibly closed edge is independent
of the minimizer when both endpoints have boundary access, as on a two-arm event. -/
theorem IsMinimizer.gradient_eq_of_endpoints_boundary_access {a : E → ℝ} {boundary : Set V}
    {data u v : V → ℝ} (hu : G.IsMinimizer a boundary data u)
    (hv : G.IsMinimizer a boundary data v) (ha : ∀ e, 0 ≤ a e) (e : E)
    (ht : ∃ z ∈ boundary, (G.positiveGraph a Set.univ).Reachable (G.tail e) z)
    (hh : ∃ z ∈ boundary, (G.positiveGraph a Set.univ).Reachable (G.head e) z) :
    G.gradient u e = G.gradient v e := by
  unfold gradient
  rw [hu.eq_of_boundary_access G hv ha hh, hu.eq_of_boundary_access G hv ha ht]

end NearCritical.Network
