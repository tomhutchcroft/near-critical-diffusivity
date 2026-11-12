module

public import NearCritical.Section10Survivor

/-! Two generic constructions for building a `NestRule`.

* `refineReveal`: a reveal with local atoms, refined by the bits on the explored
  bonds, still has local atoms on the same bonds. In the source the cluster
  union alone does not determine pre-goodness or intrinsic distances; the
  refined reveal `(G, configuration on the explored bonds)` does.
* `normIndicator`: the normalised indicator `1_A / P[A]` of a local event has
  mean one and second moment `1 / P[A]`. With `A` = "the cube is pre-good" this
  gives the site weights, with `kappa = 1/q`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- The reveal refined by the configuration on the explored bonds. -/
def refineReveal {d : ℕ} {Φ : Type*} (ρ : Configuration d × Configuration d → Φ)
    (S : Φ → Finset (LBond d)) (z : Configuration d × Configuration d) :
    Σ F : Φ, (S F → Bool) :=
  ⟨ρ z, (S (ρ z)).restrict (layerVal z)⟩

theorem refineReveal_atom_isLocal {d : ℕ} {Φ : Type*}
    (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (G : Σ F : Φ, (S F → Bool)) :
    IsLocal (S G.1) (fun z => if refineReveal ρ S z = G then (1:ℝ) else 0) := by
  obtain ⟨F, η⟩ := G
  have hiff : ∀ z, refineReveal ρ S z = ⟨F, η⟩ ↔
      (ρ z = F ∧ (S F).restrict (layerVal z) = η) := by
    intro z
    constructor
    · intro h
      have h1 : ρ z = F := congrArg Sigma.fst h
      subst h1
      exact ⟨rfl, eq_of_heq (Sigma.mk.inj h).2⟩
    · rintro ⟨h1, h2⟩
      subst h1
      subst h2
      rfl
  have hloc2 : IsLocal (S F) (fun z => if (S F).restrict (layerVal z) = η then (1:ℝ) else 0) :=
    ⟨fun b => if b = η then (1:ℝ) else 0, fun _ => rfl⟩
  have hfun : (fun z => if refineReveal ρ S z = (⟨F, η⟩ : Σ F : Φ, (S F → Bool))
      then (1:ℝ) else 0) =
      fun z => (if ρ z = F then (1:ℝ) else 0) *
        (if (S F).restrict (layerVal z) = η then (1:ℝ) else 0) := by
    funext z
    by_cases h1 : ρ z = F <;> by_cases h2 : (S F).restrict (layerVal z) = η
    · rw [if_pos ((hiff z).mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, one_mul]
    · rw [if_neg (fun h => h2 ((hiff z).mp h).2), if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 ((hiff z).mp h).1), if_neg h1, zero_mul]
    · rw [if_neg (fun h => h1 ((hiff z).mp h).1), if_neg h1, zero_mul]
  show IsLocal (S F) _
  rw [hfun]
  exact (hρ F).mul hloc2

/-- Probability of an event under the coupled law, as an integral. -/
def coupledProb {d : ℕ} (p q : unitInterval)
    (A : Set (Configuration d × Configuration d)) : ℝ :=
  ∫ z, (if z ∈ A then (1:ℝ) else 0) ∂((percolation d p).prod (percolation d q))

/-- Normalised indicator of an event. -/
def normIndicator {d : ℕ} (p q : unitInterval) (A : Set (Configuration d × Configuration d))
    (z : Configuration d × Configuration d) : ℝ :=
  (if z ∈ A then (1:ℝ) else 0) * (coupledProb p q A)⁻¹

lemma normIndicator_isLocal {d : ℕ} (p q : unitInterval) {E : Finset (LBond d)}
    {A : Set (Configuration d × Configuration d)}
    (hA : IsLocal E (fun z => if z ∈ A then (1:ℝ) else 0)) :
    IsLocal E (normIndicator p q A) :=
  hA.mul (isLocal_const E _)

lemma coupledProb_nonneg {d : ℕ} (p q : unitInterval)
    (A : Set (Configuration d × Configuration d)) : 0 ≤ coupledProb p q A :=
  integral_nonneg (fun z => by split_ifs <;> norm_num)

lemma normIndicator_nonneg {d : ℕ} (p q : unitInterval)
    (A : Set (Configuration d × Configuration d)) (z : Configuration d × Configuration d) :
    0 ≤ normIndicator p q A z :=
  mul_nonneg (by split_ifs <;> norm_num) (inv_nonneg.mpr (coupledProb_nonneg p q A))

theorem normIndicator_mean {d : ℕ} (p q : unitInterval)
    (A : Set (Configuration d × Configuration d)) (hq : 0 < coupledProb p q A) :
    (∫ z, normIndicator p q A z ∂((percolation d p).prod (percolation d q))) = 1 := by
  unfold normIndicator
  rw [integral_mul_const]
  exact mul_inv_cancel₀ hq.ne'

theorem normIndicator_sq {d : ℕ} (p q : unitInterval)
    (A : Set (Configuration d × Configuration d)) {κ : ℝ} (hκ : 0 < κ)
    (hq : κ⁻¹ ≤ coupledProb p q A) :
    (∫ z, normIndicator p q A z * normIndicator p q A z
      ∂((percolation d p).prod (percolation d q))) ≤ κ := by
  have hq0 : 0 < coupledProb p q A := lt_of_lt_of_le (inv_pos.mpr hκ) hq
  have hfun : (fun z => normIndicator p q A z * normIndicator p q A z) =
      fun z => (if z ∈ A then (1:ℝ) else 0) *
        ((coupledProb p q A)⁻¹ * (coupledProb p q A)⁻¹) := by
    funext z
    unfold normIndicator
    by_cases hz : z ∈ A
    · rw [if_pos hz]
      ring
    · rw [if_neg hz]
      ring
  rw [hfun, integral_mul_const]
  show coupledProb p q A * ((coupledProb p q A)⁻¹ * (coupledProb p q A)⁻¹) ≤ κ
  rw [← mul_assoc, mul_inv_cancel₀ hq0.ne', one_mul]
  exact (inv_le_comm₀ hq0 hκ).mpr hq

end NearCritical.Section10
