module

public import NearCritical.Section10Flow

/-! Section10 eq.nw.flow: finite conditional chain-choice averaging. Dead chains
need not carry unit flow; only contributions of nonzero weight matter. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {V E I R C : Type*} [Fintype V] [Fintype E] [Fintype I]
    [Fintype R] [Fintype C]

/-- Zero-weight summands impose no conservation or endpoint condition. -/
theorem isBoundaryUnitFlow_weighted_of_nonzero (G : Network V E) (S T : Set V)
    (α : I → ℝ) (θ : I → E → ℝ) (hα : ∑ i, α i = 1)
    (hθ : ∀ i, α i ≠ 0 → G.IsBoundaryUnitFlow S T (θ i)) :
    G.IsBoundaryUnitFlow S T (weightedFlow α θ) := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    rw [flowDivergence_weighted]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : α i = 0
    · simp [hi]
    · rw [(hθ i hi).1 v hv,mul_zero]
  · rw [faceFlux_weighted]
    calc
      _ = ∑ i, α i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : α i = 0
        · simp [hi]
        · rw [(hθ i hi).2.1,mul_one]
      _ = 1 := hα
  · rw [faceFlux_weighted]
    calc
      _ = ∑ i, -α i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : α i = 0
        · simp [hi]
        · rw [(hθ i hi).2.2,mul_neg_one]
      _ = -1 := by rw [Finset.sum_neg_distrib,hα]

theorem flowSupported_weighted_of_nonzero (a : E → ℝ) (α : I → ℝ)
    (θ : I → E → ℝ) (hθ : ∀ i, α i ≠ 0 → FlowSupported a (θ i)) :
    FlowSupported a (weightedFlow α θ) := by
  intro e he
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : α i = 0
  · simp [hi]
  · rw [hθ i hi e he,mul_zero]

/-- Product index (route, chain choices), retaining the supplied conditional
choice law kappa. Identification with the actual source law is separate. -/
def conditionalChainWeight (μ ω : R → ℝ) (κ ζ : R → C → ℝ) (i : R × C) : ℝ :=
  μ i.1*ω i.1*(κ i.1 i.2*ζ i.1 i.2)

def conditionalChainMass (μ ω : R → ℝ) (κ ζ : R → C → ℝ) : ℝ :=
  ∑ r, μ r*ω r*(∑ c, κ r c*ζ r c)

/-- The source W is exactly the total mass of flattened chain contributions. -/
theorem conditionalChainWeight_sum (μ ω : R → ℝ) (κ ζ : R → C → ℝ) :
    (∑ i, conditionalChainWeight μ ω κ ζ i) = conditionalChainMass μ ω κ ζ := by
  simp only [conditionalChainWeight,conditionalChainMass,Fintype.sum_prod_type,Finset.mul_sum]

/-- Literal conditional expectation formula for the flow, including the W
normalization. No independence or second-moment estimate is used here. -/
theorem normalized_conditional_flow_formula (μ ω : R → ℝ) (κ ζ : R → C → ℝ)
    (θ : R → C → E → ℝ) (e : E) :
    normalizedFlow (conditionalChainWeight μ ω κ ζ) (fun i => θ i.1 i.2) e =
      (∑ r, μ r*ω r*(∑ c, κ r c*ζ r c*θ r c e))/conditionalChainMass μ ω κ ζ := by
  simp only [normalizedFlow,weightedFlow,conditionalChainWeight_sum]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp only [conditionalChainWeight,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

/-- The finite conditional average carries unit boundary flux whenever W is
nonzero and surviving chains carry unit flows. Dead-chain values are arbitrary. -/
theorem normalized_conditional_boundary_unit_flow (G : Network V E) (S T : Set V)
    (μ ω : R → ℝ) (κ ζ : R → C → ℝ) (θ : R → C → E → ℝ)
    (hW : conditionalChainMass μ ω κ ζ ≠ 0)
    (hθ : ∀ r c, ζ r c ≠ 0 → G.IsBoundaryUnitFlow S T (θ r c)) :
    G.IsBoundaryUnitFlow S T
      (normalizedFlow (conditionalChainWeight μ ω κ ζ) (fun i => θ i.1 i.2)) := by
  have hsum : (∑ i, conditionalChainWeight μ ω κ ζ i) ≠ 0 := by
    rwa [conditionalChainWeight_sum]
  apply isBoundaryUnitFlow_weighted_of_nonzero
  · rw [← Finset.sum_div,div_self hsum]
  · intro i hi
    apply hθ i.1 i.2
    intro hz
    apply hi
    simp [conditionalChainWeight,hz]

/-- Physical support likewise only needs to hold for surviving chains. -/
theorem normalized_conditional_flow_supported (a : E → ℝ)
    (μ ω : R → ℝ) (κ ζ : R → C → ℝ) (θ : R → C → E → ℝ)
    (hθ : ∀ r c, ζ r c ≠ 0 → FlowSupported a (θ r c)) :
    FlowSupported a
      (normalizedFlow (conditionalChainWeight μ ω κ ζ) (fun i => θ i.1 i.2)) := by
  apply flowSupported_weighted_of_nonzero
  intro i hi
  apply hθ i.1 i.2
  intro hz
  apply hi
  simp [conditionalChainWeight,hz]

end NearCritical.Network
