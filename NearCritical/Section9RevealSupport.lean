module

public import NearCritical.NestRegularBoundary
public import NearCritical.ClusterRevealSupport

/-! Section 9 reveal support on incident bonds of the entire heart union.
The mask retains closed boundary bonds. It does not reveal all cube bonds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Changes outside the incident mask preserve every heart-root component,
and hence their union. The actual union, rather than one component, is fixed. -/
theorem heartClusterUnion_eq_of_reveal_agree {d : ℕ}
    (Q H F : Finset (Vertex d)) (hH : H ⊆ Q) {ω η : Configuration d}
    (hF : heartClusterUnion ω Q H = F)
    (hagree : ∀ e ∈ clusterRevealBonds Q F, ω e = η e) :
    heartClusterUnion η Q H = F := by
  rw [← hF]
  unfold heartClusterUnion
  apply Finset.biUnion_congr rfl
  intro root hr
  apply finiteBoxCluster_eq_of_reveal_agree Q (finiteBoxCluster ω Q root) root (hH hr) rfl
  intro e he
  have hsub : finiteBoxCluster ω Q root ⊆ F := by
    rw [← hF]
    exact cluster_subset_heartClusterUnion ω Q H hr
  obtain ⟨heQ, htQ, hx | hx⟩ := (mem_clusterRevealBonds Q _ e).mp he
  · exact hagree e ((mem_clusterRevealBonds Q F e).mpr ⟨heQ, htQ, Or.inl (hsub hx)⟩)
  · exact hagree e ((mem_clusterRevealBonds Q F e).mpr ⟨heQ, htQ, Or.inr (hsub hx)⟩)

theorem heartClusterUnion_eq_iff_reveal_agree {d : ℕ}
    (Q H F : Finset (Vertex d)) (hH : H ⊆ Q) (ω η : Configuration d)
    (hagree : ∀ e ∈ clusterRevealBonds Q F, ω e = η e) :
    heartClusterUnion ω Q H = F ↔ heartClusterUnion η Q H = F :=
  ⟨fun h => heartClusterUnion_eq_of_reveal_agree Q H F hH h hagree,
    fun h => heartClusterUnion_eq_of_reveal_agree Q H F hH h
      (fun e he => (hagree e he).symm)⟩

/-- Evaluate the literal reveal atom from exactly its explored incident bits. -/
def heartRevealLocalEvent {d : ℕ} (Q H F : Finset (Vertex d)) :
    Set (clusterRevealBonds Q F → Bool) :=
  {ξ | heartClusterUnion
    (extendConfiguration (clusterRevealBonds Q F) (fun _ => false) ξ) Q H = F}

theorem heartReveal_event_cylinder {d : ℕ}
    (Q H F : Finset (Vertex d)) (hH : H ⊆ Q) :
    {ω : Configuration d | heartClusterUnion ω Q H = F} =
      (clusterRevealBonds Q F).restrict ⁻¹' heartRevealLocalEvent Q H F := by
  ext ω
  apply heartClusterUnion_eq_iff_reveal_agree Q H F hH
  intro e he
  simp [extendConfiguration, he, Finset.restrict]

/-- A literal heart-union atom factors against all finite observables of bonds
outside its explored incident mask, including bonds still inside the cube.
No conditional independence is supplied as a hypothesis. -/
theorem heartReveal_fresh_factorization {d : ℕ} (p : unitInterval)
    (Q H F : Finset (Vertex d)) (hH : H ⊆ Q)
    (T : Finset (Bond d)) (hd : Disjoint (clusterRevealBonds Q F) T)
    (g : (T → Bool) → ℝ) :
    (∫ ω : Configuration d,
      ({η | heartClusterUnion η Q H = F} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) ω * g (T.restrict ω) ∂percolation d p) =
      (percolation d p).real {ω | heartClusterUnion ω Q H = F} *
        (∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p) := by
  let S := clusterRevealBonds Q F
  let A := heartRevealLocalEvent Q H F
  have hc := heartReveal_event_cylinder Q H F hH
  have hi : ∀ ω : Configuration d,
      ({η | heartClusterUnion η Q H = F} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) ω = A.indicator (fun _ => (1 : ℝ)) (S.restrict ω) := by
    intro ω
    rw [hc]
    rfl
  have hf := percolation_disjoint_block_integral p S T hd
    (fun z => A.indicator (fun _ => (1 : ℝ)) z.1 * g z.2)
  simp_rw [integral_const_mul] at hf
  rw [integral_mul_const] at hf
  rw [integral_finite_bernoulli, integral_finite_bernoulli,
    ← percolation_cylinder_expectation d p S (A.indicator (fun _ => (1 : ℝ))),
    ← percolation_cylinder_expectation d p T g] at hf
  simp_rw [← hi] at hf
  have hm : MeasurableSet {ω : Configuration d | heartClusterUnion ω Q H = F} := by
    rw [hc]
    exact (Set.toFinite A).measurableSet.preimage (Finset.measurable_restrict S)
  have hOne : (∫ ω : Configuration d,
      ({η | heartClusterUnion η Q H = F} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) ω ∂percolation d p) =
      (percolation d p).real {ω | heartClusterUnion ω Q H = F} := by
    exact integral_indicator_one hm
  rwa [hOne] at hf

/-- The two source reveals depend on the union of their incident masks.
This statement needs no separation of the two cubes. -/
theorem twoHeartReveal_event_cylinder {d : ℕ}
    (Q₁ H₁ F₁ Q₃ H₃ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    let S := clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃
    {ω : Configuration d | heartClusterUnion ω Q₁ H₁ = F₁ ∧
      heartClusterUnion ω Q₃ H₃ = F₃} = S.restrict ⁻¹'
      {ξ | heartClusterUnion (extendConfiguration S (fun _ => false) ξ) Q₁ H₁ = F₁ ∧
        heartClusterUnion (extendConfiguration S (fun _ => false) ξ) Q₃ H₃ = F₃} := by
  dsimp only
  ext ω
  apply and_congr
  · apply heartClusterUnion_eq_iff_reveal_agree Q₁ H₁ F₁ hH₁
    intro e he
    have heS : e ∈ clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃ :=
      Finset.mem_union.mpr (Or.inl he)
    simp [extendConfiguration, heS, Finset.restrict]
  · apply heartClusterUnion_eq_iff_reveal_agree Q₃ H₃ F₃ hH₃
    intro e he
    have heS : e ∈ clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃ :=
      Finset.mem_union.mpr (Or.inr he)
    simp [extendConfiguration, heS, Finset.restrict]

/-- Exact unnormalized freshness for the actual pair of revealed heart unions.
The zero-probability atom case is retained; conditional normalization is a
separate step. The finite fresh block may include unexplored cube bonds. -/
theorem twoHeartReveal_fresh_factorization {d : ℕ} (p : unitInterval)
    (Q₁ H₁ F₁ Q₃ H₃ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) T)
    (g : (T → Bool) → ℝ) :
    let E := {ω : Configuration d | heartClusterUnion ω Q₁ H₁ = F₁ ∧
      heartClusterUnion ω Q₃ H₃ = F₃}
    (∫ ω : Configuration d, E.indicator (fun _ => (1 : ℝ)) ω *
      g (T.restrict ω) ∂percolation d p) =
      (percolation d p).real E * (∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p) := by
  let S := clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃
  let E := {ω : Configuration d | heartClusterUnion ω Q₁ H₁ = F₁ ∧
      heartClusterUnion ω Q₃ H₃ = F₃}
  let A : Set (S → Bool) := {ξ |
    heartClusterUnion (extendConfiguration S (fun _ => false) ξ) Q₁ H₁ = F₁ ∧
    heartClusterUnion (extendConfiguration S (fun _ => false) ξ) Q₃ H₃ = F₃}
  have hc : E = S.restrict ⁻¹' A :=
    twoHeartReveal_event_cylinder Q₁ H₁ F₁ Q₃ H₃ F₃ hH₁ hH₃
  have hi : ∀ ω : Configuration d,
      E.indicator (fun _ => (1 : ℝ)) ω = A.indicator (fun _ => (1 : ℝ)) (S.restrict ω) := by
    intro ω
    rw [hc]
    rfl
  have hf := percolation_disjoint_block_integral p S T hd
    (fun z => A.indicator (fun _ => (1 : ℝ)) z.1 * g z.2)
  simp_rw [integral_const_mul] at hf
  rw [integral_mul_const] at hf
  rw [integral_finite_bernoulli, integral_finite_bernoulli,
    ← percolation_cylinder_expectation d p S (A.indicator (fun _ => (1 : ℝ))),
    ← percolation_cylinder_expectation d p T g] at hf
  simp_rw [← hi] at hf
  have hm : MeasurableSet E := by
    rw [hc]
    exact (Set.toFinite A).measurableSet.preimage (Finset.measurable_restrict S)
  have hOne : (∫ ω : Configuration d, E.indicator
      (fun _ => (1 : ℝ)) ω ∂percolation d p) = (percolation d p).real E := by
    exact integral_indicator_one hm
  rwa [hOne] at hf

end NearCritical
