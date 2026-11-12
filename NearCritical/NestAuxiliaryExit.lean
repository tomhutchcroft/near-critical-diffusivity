module

public import NearCritical.NestCoupledExit
public import NearCritical.NestRepresentativeLaw

/-! History-dependent finite auxiliary sampling in the terminal exit mean. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Every observable of finitely many bits from the two coupled samples is
integrable. No disjointness of these finite blocks is needed for integrability. -/
lemma integrable_coupled_blocks {d : ℕ} (p q : unitInterval)
    (S R T : Finset (Bond d))
    (f : ((S → Bool) × (R → Bool)) × (T → Bool) → ℝ) :
    Integrable (fun z : Configuration d × Configuration d =>
      f ((S.restrict z.1,R.restrict z.2),T.restrict z.1))
      ((percolation d p).prod (percolation d q)) := by
  have hm : Measurable (fun z : Configuration d × Configuration d =>
      ((S.restrict z.1,R.restrict z.2),T.restrict z.1)) :=
    (((Finset.measurable_restrict S).comp measurable_fst).prodMk
      ((Finset.measurable_restrict R).comp measurable_snd)).prodMk
      ((Finset.measurable_restrict T).comp measurable_fst)
  exact (Integrable.of_finite : Integrable f _).comp_measurable hm

lemma integrable_coupled_exit {d : ℕ} (p q : unitInterval) (i : Fin d)
    (S R : Finset (Bond d))
    (choose : (S → Bool) × (R → Bool) → Finset (Vertex d))
    (H : (S → Bool) × (R → Bool) → ℝ) :
    Integrable (fun z : Configuration d × Configuration d =>
      H (S.restrict z.1,R.restrict z.2) *
      (if ∃ x ∈ choose (S.restrict z.1,R.restrict z.2), z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict z.1,R.restrict z.2)).card)⁻¹ else 0))
      ((percolation d p).prod (percolation d q)) := by
  let W := (Finset.univ : Finset ((S → Bool) × (R → Bool))).biUnion choose
  have hc : ∀ η, choose η ⊆ W := by
    intro η x hx
    exact Finset.mem_biUnion.mpr ⟨η,Finset.mem_univ _,hx⟩
  have h := integrable_coupled_blocks p q S R (nestExitBondSet i W)
    (fun z => H z.1 * (if selectedExitSuccess i W (choose z.1) z.2
      then (1-(1-(p:ℝ))^(choose z.1).card)⁻¹ else 0))
  simpa only [selectedExitSuccess_restrict i W _ (hc _)] using h

/-- Finite auxiliary sampling may depend on the entire revealed pair of
histories. This unnormalized identity also allows preceding weights to depend
on the selected auxiliary outcome. -/
theorem percolation_auxiliary_exit_sum {d : ℕ} {A : Type*} [Fintype A]
    (p q : unitInterval) (hp : 0 < (p:ℝ)) (i : Fin d) (U : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (S R : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (choose : ((S → Bool) × (R → Bool)) → A → Finset (Vertex d))
    (hface : ∀ η a, ∀ x ∈ choose η a, x i = hi)
    (K H : ((S → Bool) × (R → Bool)) → A → ℝ)
    (hlive : ∀ η a, K η a ≠ 0 → H η a ≠ 0 → (choose η a).Nonempty) :
    (∫ z : Configuration d × Configuration d, ∑ a,
      (K (S.restrict z.1,R.restrict z.2) a * H (S.restrict z.1,R.restrict z.2) a) *
      (if ∃ x ∈ choose (S.restrict z.1,R.restrict z.2) a, z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict z.1,R.restrict z.2) a).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z : Configuration d × Configuration d, ∑ a,
        K (S.restrict z.1,R.restrict z.2) a * H (S.restrict z.1,R.restrict z.2) a
        ∂((percolation d p).prod (percolation d q)) := by
  rw [integral_finsetSum]
  · rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a _ha
      exact percolation_coupled_exit_weighted_mean p q hp i U hU S R hS
        (fun η => choose η a) (fun η => hface η a) (fun η => K η a * H η a)
        (fun η hη => hlive η a (mul_ne_zero_iff.mp hη).1 (mul_ne_zero_iff.mp hη).2)
    · intro a _ha
      simpa only using integrable_coupled_blocks p q S R ∅ (fun z => K z.1 a * H z.1 a)
  · intro a _ha
    exact integrable_coupled_exit p q i S R (fun η => choose η a) (fun η => K η a * H η a)

/-- A genuine finite conditional probability law contributes no extra factor
to the mean. Its dependence on revealed histories is unrestricted. -/
theorem percolation_auxiliary_exit_weighted_mean {d : ℕ} {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p q : unitInterval) (hp : 0 < (p:ℝ)) (i : Fin d) (U : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (S R : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (choose : ((S → Bool) × (R → Bool)) → A → Finset (Vertex d))
    (hface : ∀ η a, ∀ x ∈ choose η a, x i = hi)
    (law : ((S → Bool) × (R → Bool)) → Measure A)
    (hprob : ∀ η, IsProbabilityMeasure (law η)) (H : (S → Bool) × (R → Bool) → ℝ)
    (hlive : ∀ η a, (law η).real {a} ≠ 0 → H η ≠ 0 → (choose η a).Nonempty) :
    (∫ z : Configuration d × Configuration d, ∑ a,
      ((law (S.restrict z.1,R.restrict z.2)).real {a} * H (S.restrict z.1,R.restrict z.2)) *
      (if ∃ x ∈ choose (S.restrict z.1,R.restrict z.2) a, z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict z.1,R.restrict z.2) a).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z : Configuration d × Configuration d, H (S.restrict z.1,R.restrict z.2)
        ∂((percolation d p).prod (percolation d q)) := by
  have h := percolation_auxiliary_exit_sum p q hp i U hU S R hS choose hface
    (fun η a => (law η).real {a}) (fun η _ => H η) hlive
  have hrow (η : (S → Bool) × (R → Bool)) : ∑ a, (law η).real {a} = 1 := by
    have := hprob η
    simp
  simp_rw [← Finset.sum_mul,hrow,one_mul] at h
  exact h

/-- Instantiation with the previously constructed first-good-representative,
uniform-next-nest trace law. Offspring and starting nest may depend on BOTH
revealed histories; no abstract probability-row hypothesis remains. -/
theorem percolation_representative_exit_weighted_mean {d : ℕ} {α : Type*}
    [Fintype α] [LinearOrder α] [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]
    (p q : unitInterval) (hp : 0 < (p:ℝ)) (i : Fin d) (U : Finset (Vertex d)) {hi : ℤ}
    (hU : ∀ x ∈ U, x i ≤ hi) (S R : Finset (Bond d)) (hS : S ⊆ internalBondSet U)
    (offspring : ((S → Bool) × (R → Bool)) → ℕ → Finset α → α → Finset α)
    (k N : ℕ) (hk : k ≤ Fintype.card α) (start : ((S → Bool) × (R → Bool)) → Finset α)
    (choose : ((S → Bool) × (R → Bool)) → NestTrace (Finset α) N → Finset (Vertex d))
    (hface : ∀ η a, ∀ x ∈ choose η a, x i = hi) (H : (S → Bool) × (R → Bool) → ℝ)
    (hlive : ∀ η a, ((representativeTraceLaw (offspring η) k N hk (start η)).toMeasure).real {a} ≠ 0 →
      H η ≠ 0 → (choose η a).Nonempty) :
    (∫ z : Configuration d × Configuration d, ∑ a,
      (((representativeTraceLaw (offspring (S.restrict z.1,R.restrict z.2)) k N hk
        (start (S.restrict z.1,R.restrict z.2))).toMeasure).real {a} * H (S.restrict z.1,R.restrict z.2)) *
      (if ∃ x ∈ choose (S.restrict z.1,R.restrict z.2) a, z.1 (x,i) = true
       then (1-(1-(p:ℝ))^(choose (S.restrict z.1,R.restrict z.2) a).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z : Configuration d × Configuration d, H (S.restrict z.1,R.restrict z.2)
        ∂((percolation d p).prod (percolation d q)) := by
  exact percolation_auxiliary_exit_weighted_mean p q hp i U hU S R hS choose hface
    (fun η => (representativeTraceLaw (offspring η) k N hk (start η)).toMeasure)
    (fun _ => inferInstance) H hlive

end NearCritical
