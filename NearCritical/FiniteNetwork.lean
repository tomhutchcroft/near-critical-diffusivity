module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-! Finite weighted networks underlying equations (3.1), (3.12), and Lemma 4.1.
The boundary set is explicit: full and two-face boundary data are different inputs.
No existence or uniqueness of a minimizer is presumed. -/
@[expose] public section

namespace NearCritical

structure Network (V E : Type*) where
  tail : E → V
  head : E → V

namespace Network
variable {V E : Type*} [Fintype E] (G : Network V E)

def gradient (u : V → ℝ) (e : E) : ℝ := u (G.head e) - u (G.tail e)

def energy (a : E → ℝ) (u : V → ℝ) : ℝ :=
  ∑ e, a e * (G.gradient u e) ^ 2

def admissible (boundary : Set V) (data u : V → ℝ) : Prop :=
  ∀ x ∈ boundary, u x = data x

def IsMinimizer (a : E → ℝ) (boundary : Set V) (data u : V → ℝ) : Prop :=
  admissible boundary data u ∧
    ∀ v, admissible boundary data v → G.energy a u ≤ G.energy a v

lemma energy_nonneg {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) (u : V → ℝ) :
    0 ≤ G.energy a u := by
  exact Finset.sum_nonneg (fun e _ ↦ mul_nonneg (ha e) (sq_nonneg _))

lemma energy_mono {a b : E → ℝ} (hab : ∀ e, a e ≤ b e) (u : V → ℝ) :
    G.energy a u ≤ G.energy b u := by
  exact Finset.sum_le_sum (fun e _ ↦ mul_le_mul_of_nonneg_right (hab e) (sq_nonneg _))

lemma energy_sub (a b : E → ℝ) (u : V → ℝ) :
    G.energy (b - a) u = G.energy b u - G.energy a u := by
  simp only [energy, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The two variational bounds in `lem.comparison`, before volume normalization. -/
theorem minimizer_comparison {a b : E → ℝ} {boundary : Set V} {data u v : V → ℝ}
    (hu : G.IsMinimizer a boundary data u) (hv : G.IsMinimizer b boundary data v) :
    G.energy (b - a) v ≤ G.energy b v - G.energy a u ∧
      G.energy b v - G.energy a u ≤ G.energy (b - a) u := by
  rw [G.energy_sub, G.energy_sub]
  constructor
  · linarith [hu.2 v hv.1]
  · linarith [hv.2 u hu.1]

/-- Rayleigh monotonicity for arbitrary fixed Dirichlet boundary data. -/
theorem minimizer_mono {a b : E → ℝ} {boundary : Set V} {data u v : V → ℝ}
    (hab : ∀ e, a e ≤ b e)
    (hu : G.IsMinimizer a boundary data u) (hv : G.IsMinimizer b boundary data v) :
    G.energy a u ≤ G.energy b v :=
  (hu.2 v hv.1).trans (G.energy_mono hab v)

/-- Relaxing the boundary condition lowers the minimum (`eq.chain.low`). -/
theorem minimizer_boundary_mono {a : E → ℝ} {small large : Set V} {data u v : V → ℝ}
    (hsub : small ⊆ large)
    (hu : G.IsMinimizer a small data u) (hv : G.IsMinimizer a large data v) :
    G.energy a u ≤ G.energy a v := by
  exact hu.2 v (fun x hx ↦ hv.1 x (hsub hx))

/-- The variational energy itself, without choosing any minimizer. -/
noncomputable def conductance (a : E → ℝ) (boundary : Set V) (data : V → ℝ) : ℝ :=
  sInf {r | ∃ u, admissible boundary data u ∧ G.energy a u = r}

lemma energyValues_nonempty (a : E → ℝ) (boundary : Set V) (data : V → ℝ) :
    {r | ∃ u, admissible boundary data u ∧ G.energy a u = r}.Nonempty :=
  ⟨G.energy a data, data, (fun _ _ ↦ rfl), rfl⟩

lemma energyValues_bddBelow {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) :
    BddBelow {r | ∃ u, admissible boundary data u ∧ G.energy a u = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨u, _, rfl⟩
  exact G.energy_nonneg ha u

lemma conductance_nonneg {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (boundary : Set V) (data : V → ℝ) :
    0 ≤ G.conductance a boundary data := by
  apply le_csInf (G.energyValues_nonempty a boundary data)
  rintro r ⟨u, _, rfl⟩
  exact G.energy_nonneg ha u

lemma conductance_le_energy {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    {boundary : Set V} {data u : V → ℝ} (hu : admissible boundary data u) :
    G.conductance a boundary data ≤ G.energy a u :=
  csInf_le (G.energyValues_bddBelow ha boundary data) ⟨u, hu, rfl⟩

/-- Rayleigh monotonicity directly for the variational infimum. -/
theorem conductance_mono {a b : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (hab : ∀ e, a e ≤ b e) (boundary : Set V) (data : V → ℝ) :
    G.conductance a boundary data ≤ G.conductance b boundary data := by
  apply le_csInf (G.energyValues_nonempty b boundary data)
  rintro r ⟨u, hu, rfl⟩
  exact (G.conductance_le_energy ha hu).trans (G.energy_mono hab u)

/-- `eq.chain.low` for the actual infima, including degenerate conductances. -/
theorem conductance_boundary_mono {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    {small large : Set V} (hsub : small ⊆ large) (data : V → ℝ) :
    G.conductance a small data ≤ G.conductance a large data := by
  apply le_csInf (G.energyValues_nonempty a large data)
  rintro r ⟨u, hu, rfl⟩
  exact G.conductance_le_energy ha (fun x hx ↦ hu x (hsub hx))

lemma IsMinimizer.conductance_eq {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    {boundary : Set V} {data u : V → ℝ} (hu : G.IsMinimizer a boundary data u) :
    G.conductance a boundary data = G.energy a u := by
  apply le_antisymm (G.conductance_le_energy ha hu.1)
  apply le_csInf (G.energyValues_nonempty a boundary data)
  rintro r ⟨v, hv, rfl⟩
  exact hu.2 v hv

end Network
end NearCritical
