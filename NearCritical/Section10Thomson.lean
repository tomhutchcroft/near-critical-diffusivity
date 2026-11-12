module

public import NearCritical.Section10Flow

/-! Section10: the deterministic energy comparison used after the random flow
has been constructed. Closed-edge support is retained explicitly. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {V E : Type*} [Fintype V] [Fintype E]

lemma flow_divergence_pairing (G : Network V E) (θ : E → ℝ) (u : V → ℝ) :
    (∑ v, u v*G.flowDivergence θ v) = ∑ e, θ e*(u (G.tail e)-u (G.head e)) := by
  calc
    _ = ∑ e, ∑ v, u v*((if G.tail e = v then (1:ℝ) else 0)-
        (if G.head e = v then (1:ℝ) else 0))*θ e := by
      simp only [flowDivergence,Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      simp [mul_sub,sub_mul,mul_ite,ite_mul,Finset.sum_sub_distrib]
      <;> ring

lemma flow_summation_by_parts (G : Network V E) (θ : E → ℝ) (u : V → ℝ) :
    (∑ e, θ e*G.gradient u e) = -(∑ v, u v*G.flowDivergence θ v) := by
  rw [flow_divergence_pairing,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  simp only [gradient]
  ring

/-- Unit total flux and constant values on the two faces determine the work,
without requiring each path to have the same endpoint. -/
theorem boundary_unit_flow_work (G : Network V E) (S T : Set V)
    (θ : E → ℝ) (hθ : G.IsBoundaryUnitFlow S T θ)
    (u : V → ℝ) (H : ℝ) (hS : ∀ v ∈ S, u v = 0) (hT : ∀ v ∈ T, u v = H) :
    (∑ e, θ e*G.gradient u e) = H := by
  have hp (v : V) : u v*G.flowDivergence θ v =
      if v ∈ T then H*G.flowDivergence θ v else 0 := by
    by_cases ht : v ∈ T
    · simp only [if_pos ht,hT v ht]
    · by_cases hs : v ∈ S
      · simp only [if_neg ht,hS v hs,zero_mul]
      · have hd := hθ.1 v (by simp [hs,ht])
        simp only [hd,mul_zero,if_neg ht]
  have hcharge : (∑ v, u v*G.flowDivergence θ v) = -H := by
    calc
      _ = ∑ v, if v ∈ T then H*G.flowDivergence θ v else 0 := Finset.sum_congr rfl (fun v _ => hp v)
      _ = H*(∑ v ∈ Finset.univ.filter (fun v => v ∈ T), G.flowDivergence θ v) := by
        simp only [Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
      _ = -H := by rw [hθ.2.2]; ring
  rw [flow_summation_by_parts,hcharge,neg_neg]

/-- Weighted Cauchy inequality for the ACTUAL Dirichlet and resistance
energies, including zero conductances with zero supported current. -/
theorem flow_work_sq_le_energy_product (G : Network V E)
    (a θ : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hsupport : FlowSupported a θ) (u : V → ℝ) :
    (∑ e, θ e*G.gradient u e)^2 ≤ G.energy a u*flowEnergy a θ := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun e => a e*(G.gradient u e)^2) (g := fun e => (θ e)^2/a e)
    (fun e _ => mul_nonneg (ha e) (sq_nonneg _))
    (fun e _ => div_nonneg (sq_nonneg _) (ha e))
  intro e _he
  by_cases hz : a e = 0
  · simp [hz,hsupport e hz]
  · have heq : (θ e*G.gradient u e)^2 = (a e*(G.gradient u e)^2)*((θ e)^2/a e) := by
      field_simp [hz]
      <;> ring
    exact heq.le

/-- The finite-network Thomson inequality needed by source Section10 is
DERIVED, with no effective-resistance comparison as a premise. -/
theorem boundary_unit_flow_energy_lower (G : Network V E) (S T : Set V)
    (a θ : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hsupport : FlowSupported a θ)
    (hθ : G.IsBoundaryUnitFlow S T θ) (u : V → ℝ) (H : ℝ)
    (hS : ∀ v ∈ S, u v = 0) (hT : ∀ v ∈ T, u v = H) :
    H^2 ≤ G.energy a u*flowEnergy a θ := by
  have h := flow_work_sq_le_energy_product G a θ ha hsupport u
  rwa [boundary_unit_flow_work G S T θ hθ u H hS hT] at h

/-- Positive boundary separation forces positive flow energy, so the final
Dirichlet lower bound does not rely on totalized division at zero. -/
theorem boundary_unit_flow_energy_div_lower (G : Network V E) (S T : Set V)
    (a θ : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hsupport : FlowSupported a θ)
    (hθ : G.IsBoundaryUnitFlow S T θ) (u : V → ℝ) (H : ℝ) (hH : H ≠ 0)
    (hS : ∀ v ∈ S, u v = 0) (hT : ∀ v ∈ T, u v = H) :
    0 < flowEnergy a θ ∧ H^2/flowEnergy a θ ≤ G.energy a u := by
  have hb := boundary_unit_flow_energy_lower G S T a θ ha hsupport hθ u H hS hT
  have hn : 0 ≤ flowEnergy a θ := Finset.sum_nonneg (fun e _ => div_nonneg (sq_nonneg _) (ha e))
  have hp : 0 < flowEnergy a θ := by
    by_contra h
    have hz : flowEnergy a θ = 0 := le_antisymm (le_of_not_gt h) hn
    have hsq : 0 < H^2 := sq_pos_of_ne_zero hH
    rw [hz,mul_zero] at hb
    linarith
  exact ⟨hp,(div_le_iff₀ hp).mpr hb⟩

end NearCritical.Network
