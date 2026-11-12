module

public import NearCritical.NestExitLaw

/-! Adaptive terminal exit selection from a finite revealed interior history.
The chosen boundary set may vary arbitrarily with that history. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Success of a selected subset, observed through a common finite exit pool. -/
def selectedExitSuccess {d : ℕ} (i : Fin d) (W V : Finset (Vertex d))
    (ξ : nestExitBondSet i W → Bool) : Prop :=
  ∃ x, ∃ hx : (x,i) ∈ nestExitBondSet i W, x ∈ V ∧ ξ ⟨(x,i),hx⟩ = true

lemma selectedExitSuccess_restrict {d : ℕ} (i : Fin d) (W V : Finset (Vertex d))
    (hVW : V ⊆ W) (ω : Configuration d) :
    selectedExitSuccess i W V ((nestExitBondSet i W).restrict ω) ↔
      ∃ x ∈ V, ω (x,i) = true := by
  constructor
  · rintro ⟨x,hx,hV,hopen⟩
    exact ⟨x,hV,hopen⟩
  · rintro ⟨x,hV,hopen⟩
    exact ⟨x,Finset.mem_image.mpr ⟨x,hVW hV,rfl⟩,hV,hopen⟩

/-- Restricting the actual law to a common pool preserves the exact selected
subset OR probability; unused pool coordinates cause no independence premise. -/
lemma selectedExitSuccess_probability {d : ℕ} (p : unitInterval) (i : Fin d)
    (W V : Finset (Vertex d)) (hVW : V ⊆ W) :
    (Measure.pi (fun _ : nestExitBondSet i W => bernoulliMeasure true false p)).real
      {ξ | selectedExitSuccess i W V ξ} = 1-(1-(p:ℝ))^V.card := by
  have hm : (percolation d p).map (nestExitBondSet i W).restrict =
      Measure.pi (fun _ : nestExitBondSet i W => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  rw [← hm,map_measureReal_apply (Finset.measurable_restrict _) (Set.toFinite _).measurableSet]
  have he : ((nestExitBondSet i W).restrict : Configuration d → _) ⁻¹'
      {ξ | selectedExitSuccess i W V ξ} = {ω | ∃ x ∈ V, ω (x,i) = true} := by
    ext ω
    exact selectedExitSuccess_restrict i W V hVW ω
  rw [he,percolation_exit_success_probability]

/-- Exact mean identity for adaptive exit selection. The common pool lies on
the upper face, whereas the revealed block is internal. Empty choices are
permitted on histories where the preceding weight vanishes. -/
theorem percolation_adaptive_exit_weighted_mean {d : ℕ} (p : unitInterval)
    (hp : 0 < (p:ℝ)) (i : Fin d) (U W : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (hW : ∀ x ∈ W, x i = hi)
    (S : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (choose : (S → Bool) → Finset (Vertex d)) (hchoose : ∀ η, choose η ⊆ W)
    (H : (S → Bool) → ℝ) (hlive : ∀ η, H η ≠ 0 → (choose η).Nonempty) :
    (∫ ω : Configuration d, H (S.restrict ω) *
      (if ∃ x ∈ choose (S.restrict ω), ω (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict ω)).card)⁻¹ else 0)
      ∂percolation d p) = ∫ ω : Configuration d, H (S.restrict ω) ∂percolation d p := by
  let T := nestExitBondSet i W
  let success := fun η ξ => selectedExitSuccess i W (choose η) ξ
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e heS heT
    exact Finset.disjoint_left.mp (nestExitBondSet_disjoint_internal i U W hU hW)
      heT (hS heS)
  have hq (η : S → Bool) : freshTubeSuccessProbability p S T success η =
      1-(1-(p:ℝ))^(choose η).card :=
    selectedExitSuccess_probability p i W (choose η) (hchoose η)
  have hpos (η : S → Bool) (hη : H η ≠ 0) :
      0 < freshTubeSuccessProbability p S T success η := by
    rw [hq]
    exact exit_success_probability_pos p hp _ (hlive η hη)
  have h := percolation_freshTube_weighted_mean_on_support p S T hd success H hpos
  have he (ω : Configuration d) : freshTubeSuccessWeight p S T success
      (S.restrict ω) (T.restrict ω) =
      (if ∃ x ∈ choose (S.restrict ω), ω (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict ω)).card)⁻¹ else 0) := by
    unfold freshTubeSuccessWeight
    rw [hq]
    have hex := selectedExitSuccess_restrict i W (choose (S.restrict ω))
      (hchoose _) ω
    simp only [success,T,hex]
  simpa only [he] using h

/-- No preassigned pool is needed: finite revealed histories give a finite
union of all candidate exit sets, and face geometry makes this whole pool fresh. -/
theorem percolation_adaptive_exit_weighted_mean_of_face {d : ℕ} (p : unitInterval)
    (hp : 0 < (p:ℝ)) (i : Fin d) (U : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (S : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (choose : (S → Bool) → Finset (Vertex d))
    (hface : ∀ η, ∀ x ∈ choose η, x i = hi)
    (H : (S → Bool) → ℝ) (hlive : ∀ η, H η ≠ 0 → (choose η).Nonempty) :
    (∫ ω : Configuration d, H (S.restrict ω) *
      (if ∃ x ∈ choose (S.restrict ω), ω (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict ω)).card)⁻¹ else 0)
      ∂percolation d p) = ∫ ω : Configuration d, H (S.restrict ω) ∂percolation d p := by
  let W := (Finset.univ : Finset (S → Bool)).biUnion choose
  have hW : ∀ x ∈ W, x i = hi := by
    intro x hx
    obtain ⟨η,_,hη⟩ := Finset.mem_biUnion.mp hx
    exact hface η x hη
  have hchoose : ∀ η, choose η ⊆ W := by
    intro η x hx
    exact Finset.mem_biUnion.mpr ⟨η,Finset.mem_univ _,hx⟩
  exact percolation_adaptive_exit_weighted_mean p hp i U W hU hW S hS choose hchoose H hlive

end NearCritical
