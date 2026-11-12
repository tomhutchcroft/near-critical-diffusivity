module

public import NearCritical.FiniteNetwork
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

/-! Section10, eq.nw.flow: averaging flows with variable boundary endpoints.
Boundary flux, rather than a fixed vertexwise charge, is essential because
individual chain paths can start and finish at different face vertices. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

/-- Outgoing minus incoming current, in the network's fixed edge orientation. -/
def flowDivergence (G : Network V E) (θ : E → ℝ) (v : V) : ℝ :=
  ∑ e, ((if G.tail e = v then (1:ℝ) else 0) -
    (if G.head e = v then (1:ℝ) else 0))*θ e

/-- Unit flow between two boundary faces; endpoint charges need not coincide
between paths. Interior divergence vanishes and total face fluxes are plus one and minus one. -/
def IsBoundaryUnitFlow (G : Network V E) (S T : Set V) (θ : E → ℝ) : Prop :=
  (∀ v, v ∉ S ∪ T → G.flowDivergence θ v = 0) ∧
    (∑ v ∈ Finset.univ.filter (fun v => v ∈ S), G.flowDivergence θ v) = 1 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v ∈ T), G.flowDivergence θ v) = -1

def weightedFlow (α : I → ℝ) (θ : I → E → ℝ) (e : E) : ℝ := ∑ i, α i*θ i e

def normalizedFlow (w : I → ℝ) (θ : I → E → ℝ) : E → ℝ :=
  weightedFlow (fun i => w i/(∑ j, w j)) θ

/-- The physical resistance energy, with support on zero-conductance edges
handled separately rather than inferred from real division by zero. -/
def flowEnergy (a : E → ℝ) (θ : E → ℝ) : ℝ := ∑ e, (θ e)^2/a e

def FlowSupported (a : E → ℝ) (θ : E → ℝ) : Prop := ∀ e, a e = 0 → θ e = 0

lemma flowDivergence_weighted (G : Network V E) (α : I → ℝ) (θ : I → E → ℝ) (v : V) :
    G.flowDivergence (weightedFlow α θ) v = ∑ i, α i*G.flowDivergence (θ i) v := by
  simp only [flowDivergence,weightedFlow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro e _he
  ring

lemma faceFlux_weighted (G : Network V E) (S : Finset V) (α : I → ℝ) (θ : I → E → ℝ) :
    (∑ v ∈ S, G.flowDivergence (weightedFlow α θ) v) =
      ∑ i, α i*(∑ v ∈ S, G.flowDivergence (θ i) v) := by
  simp_rw [flowDivergence_weighted]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Source weighted averaging preserves unit boundary flux even when path
endpoints differ. Normalization, not positivity, is the linear requirement. -/
theorem isBoundaryUnitFlow_weighted (G : Network V E) (S T : Set V)
    (α : I → ℝ) (θ : I → E → ℝ) (hα : ∑ i, α i = 1)
    (hθ : ∀ i, G.IsBoundaryUnitFlow S T (θ i)) :
    G.IsBoundaryUnitFlow S T (weightedFlow α θ) := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    rw [flowDivergence_weighted]
    simp only [(fun i => (hθ i).1 v hv),mul_zero,Finset.sum_const_zero]
  · rw [faceFlux_weighted]
    simp only [(fun i => (hθ i).2.1),mul_one]
    exact hα
  · rw [faceFlux_weighted]
    simp only [(fun i => (hθ i).2.2),mul_neg_one,Finset.sum_neg_distrib,hα]

theorem isBoundaryUnitFlow_normalized (G : Network V E) (S T : Set V)
    (w : I → ℝ) (θ : I → E → ℝ) (hW : (∑ i, w i) ≠ 0)
    (hθ : ∀ i, G.IsBoundaryUnitFlow S T (θ i)) :
    G.IsBoundaryUnitFlow S T (normalizedFlow w θ) := by
  apply isBoundaryUnitFlow_weighted G S T _ θ _ hθ
  rw [← Finset.sum_div, div_self hW]

lemma flowSupported_weighted (a : E → ℝ) (α : I → ℝ) (θ : I → E → ℝ)
    (hθ : ∀ i, FlowSupported a (θ i)) : FlowSupported a (weightedFlow α θ) := by
  intro e he
  simp only [weightedFlow,(fun i => hθ i e he),mul_zero,Finset.sum_const_zero]

/-- Exact pair expansion underlying the random-flow energy estimate. This
identity needs no independence or moment estimate and loses no diagonal terms. -/
theorem flowEnergy_weighted_pairs (a : E → ℝ) (α : I → ℝ) (θ : I → E → ℝ) :
    flowEnergy a (weightedFlow α θ) =
      ∑ i, ∑ j, α i*α j*(∑ e, θ i e*θ j e/a e) := by
  simp only [flowEnergy,weightedFlow,pow_two,Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro e _he
  ring

end NearCritical.Network
