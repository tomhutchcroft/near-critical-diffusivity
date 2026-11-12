module

public import NearCritical.Section10SharedPhasePersistence
public import NearCritical.Section10ChainMean

/-! The nonterminal phase contraction for normalized first-good nest
transition rows, including the independent sign choices. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- When the next choices are a product of nests and both signs, the
stored next sign can equivalently be drawn independently at the next step. -/
theorem stepKernel_fair_nextSign {d : ℕ} {X : Type*} (T : Finset (LBond d))
    (A : Set (T → Bool)) (O : (T → Bool) → Finset X) (s : ℝ)
    (y : X) (b : Bool) (z : Configuration d × Configuration d) :
    stepKernel T A (fun ξ => (O ξ).product (Finset.univ : Finset Bool)) s (y,b) z =
      stepKernel T A O s y z / 2 := by
  simp only [stepKernel, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.card_product, Finset.card_univ, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  split_ifs
  · rw [← mul_assoc, mul_inv_rev, div_eq_mul_inv, mul_comm]
  · norm_num

private theorem stepKernel_row_range {d : ℕ} {X : Type*} [Fintype X]
    (T : Finset (LBond d)) (A : Set (T → Bool)) (O : (T → Bool) → Finset X)
    (hO : ∀ ξ ∈ A, (O ξ).Nonempty) {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ) (hi : s⁻¹ ≤ ρ)
    (z : Configuration d × Configuration d) :
    0 ≤ (∑ y, stepKernel T A O s y z) ∧ (∑ y, stepKernel T A O s y z) ≤ ρ := by
  rw [stepKernel_sum _ _ _ hO]
  by_cases h : T.restrict (layerVal z) ∈ A
  · simpa only [if_pos h, one_mul] using And.intro (inv_nonneg.mpr hs) hi
  · simp [h, hρ]

/-- After independent fair signs and summing the next-nest choices, the
actual joint normalized transition charges at most two thirds to a
noncleaning shared tube. The event uses the union over possible bridge
representatives, so the representative may be selected using the tube. -/
theorem shared_stepKernel_persistence_le {d : ℕ} {ι ι' X X' : Type*} [Fintype X] [Fintype X']
    (μ : Measure (Configuration d × Configuration d)) [IsProbabilityMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (J' : Finset ι') (P : Bool → ι → Finset (Vertex d))
    (P' : Bool → ι' → Finset (Vertex d))
    (T : Finset (LBond d)) (A A' : Bool → Set (T → Bool))
    (O : Bool → (T → Bool) → Finset X) (O' : Bool → (T → Bool) → Finset X')
    (hO : ∀ a ξ, ξ ∈ A a → (O a ξ).Nonempty)
    (hO' : ∀ a ξ, ξ ∈ A' a → (O' a ξ).Nonempty)
    (s s' : Bool → ℝ) {ε k : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4)
    (hs : ∀ a, 0 ≤ s a ∧ (s a)⁻¹ ≤ 1+ε/2)
    (hs' : ∀ a, 0 ≤ s' a ∧ (s' a)⁻¹ ≤ 1+ε/2)
    (hk : (J.card:ℝ) * (J'.card:ℝ) * k ≤ 1/40)
    (hpair : ∀ a b, a ≠ b → ∀ x ∈ J, ∀ y ∈ J', μ.real {z |
      (section9SprinklingCluster z.1 z.2 E L R Q₁ F₁ Q₃ F₃ (P a x) B ∩
        section9SprinklingCluster z.1 z.2 E L R Q₁ F₁ Q₃ F₃ (P' b y) B).Nonempty} ≤ k) :
    let N a b := if a = b then Set.univ else bridgeNestMeetEvent E L R Q₁ F₁ Q₃ F₃ B J J' (P a) (P' b)
    (∑ a : Bool, ∑ b : Bool, ∫ z, (N a b).indicator (fun z =>
      ∑ yy : X × X', stepKernel T (A a) (O a) (s a) yy.1 z *
        stepKernel T (A' b) (O' b) (s' b) yy.2 z) z ∂μ) / 4 ≤ 2/3 := by
  intro N
  refine shared_phase_persistence_le μ E L R Q₁ F₁ Q₃ F₃ B J J' P P' _ hε hsmall ?_ hk hpair
  intro a b z
  have hρ : 0 ≤ 1+ε/2 := by linarith
  have h := stepKernel_row_range T (A a) (O a) (hO a) (hs a).1 hρ (hs a).2 z
  have h' := stepKernel_row_range T (A' b) (O' b) (hO' b) (hs' b).1 hρ (hs' b).2 z
  simp only [Fintype.sum_prod_type, Prod.fst, Prod.snd, ← Fintype.sum_mul_sum, pow_two]
  exact ⟨mul_nonneg h.1 h'.1, mul_le_mul h.2 h'.2 h'.1 hρ⟩

end NearCritical.Section10
