module

public import NearCritical.FiniteNetwork
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace NearCritical.Network
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

def pairing (a : E → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ e, a e * G.gradient u e * G.gradient v e

lemma pairing_self (a : E → ℝ) (u : V → ℝ) :
    G.pairing a u u = G.energy a u := by
  unfold pairing energy
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma pairing_comm (a : E → ℝ) (u v : V → ℝ) :
    G.pairing a u v = G.pairing a v u := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma energy_variation (a : E → ℝ) (u w : V → ℝ) (t : ℝ) :
    G.energy a (u + t • w) =
      G.energy a u + 2 * t * G.pairing a w u + t ^ 2 * G.energy a w := by
  simp only [energy, pairing, gradient, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The Euler equation with zero Dirichlet variations. -/
def IsHarmonic (a : E → ℝ) (boundary : Set V) (u : V → ℝ) : Prop :=
  ∀ w : V → ℝ, (∀ x ∈ boundary, w x = 0) → G.pairing a w u = 0

/-- Every energy minimizer satisfies the weak harmonic equation, including
networks with zero conductances and nonunique minimizers. -/
theorem IsMinimizer.isHarmonic {a : E → ℝ} {boundary : Set V} {data u : V → ℝ}
    (hu : G.IsMinimizer a boundary data u) : G.IsHarmonic a boundary u := by
  intro w hw
  have hp : ∀ t : ℝ, 0 ≤ G.energy a w * (t * t) + (2 * G.pairing a w u) * t + 0 := by
    intro t
    have hm := hu.2 (u + t • w) (by
      intro x hx
      simp [Pi.add_apply, Pi.smul_apply, hw x hx, hu.1 x hx])
    rw [G.energy_variation] at hm
    nlinarith
  have hd := discrim_le_zero hp
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg (G.pairing a w u)]

/-- The mixed identity in `eq.difference_comparison`. -/
theorem minimizer_mixed_identity {a b : E → ℝ} {boundary : Set V} {data u v : V → ℝ}
    (hu : G.IsMinimizer a boundary data u) (hv : G.IsMinimizer b boundary data v) :
    G.energy b v - G.energy a u = G.pairing (b - a) v u := by
  have hz : ∀ x ∈ boundary, (v - u) x = 0 := by
    intro x hx
    simp [hv.1 x hx, hu.1 x hx]
  have h1 := hu.isHarmonic G (v - u) hz
  have h2 := hv.isHarmonic G (v - u) hz
  have heq (c : E → ℝ) :
      G.pairing c (v - u) u = G.pairing c v u - G.energy c u := by
    simp only [pairing, energy, gradient, Pi.sub_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have heq' (c : E → ℝ) :
      G.pairing c (v - u) v = G.energy c v - G.pairing c v u := by
    simp only [pairing, energy, gradient, Pi.sub_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq] at h1
  rw [heq'] at h2
  have hp : G.pairing (b - a) v u = G.pairing b v u - G.pairing a v u := by
    simp only [pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hp]
  linarith

/-- The full comparison formula with the paper's positive volume normalization. -/
theorem normalized_minimizer_comparison {a b : E → ℝ} {boundary : Set V}
    {data u v : V → ℝ} {volume : ℝ} (hvol : 0 < volume)
    (hu : G.IsMinimizer a boundary data u) (hv : G.IsMinimizer b boundary data v) :
    G.energy (b - a) v / volume ≤
        (G.energy b v - G.energy a u) / volume ∧
    (G.energy b v - G.energy a u) / volume = G.pairing (b - a) v u / volume ∧
    (G.energy b v - G.energy a u) / volume ≤ G.energy (b - a) u / volume := by
  obtain ⟨hlo, hhi⟩ := G.minimizer_comparison hu hv
  exact ⟨div_le_div_of_nonneg_right hlo hvol.le,
    congrArg (fun r : ℝ ↦ r / volume) (G.minimizer_mixed_identity hu hv),
    div_le_div_of_nonneg_right hhi hvol.le⟩

end NearCritical.Network
