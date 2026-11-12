module

public import NearCritical.NestUniformChoice

/-! The two independently drawn initial nests before any tube is explored. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical ENNReal

variable {α : Type*} [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]

/-- The exact spread probability for prescribed members of the two
independent uniform nests, allowing the two prescribed clusters to coincide. -/
theorem initial_nest_joint_membership_probability (S : Finset α) {k : ℕ}
    (hk₀ : 1 ≤ k) (hk : k ≤ S.card) {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    ((uniformNestChoice S k).prod (uniformNestChoice S k)).real
      {J : Finset α × Finset α | x ∈ J.1 ∧ y ∈ J.2} = ((k:ℝ)/S.card)^2 := by
  letI := uniformNestChoice_probability S k hk
  change ((uniformNestChoice S k).prod (uniformNestChoice S k)).real
    ({J : Finset α | x ∈ J} ×ˢ {J : Finset α | y ∈ J}) = _
  calc
    _ = (uniformNestChoice S k).real {J : Finset α | x ∈ J} *
        (uniformNestChoice S k).real {J : Finset α | y ∈ J} := by
      simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    _ = _ := by
      rw [uniformNestChoice_mem_probability S hk₀ hk hx, uniformNestChoice_mem_probability S hk₀ hk hy,
        pow_two]

/-- Before the initial draw is revealed, the two nests share a cluster
with probability at most k² divided by the number of available clusters. -/
theorem initial_nest_intersection_probability_le (S : Finset α) {k : ℕ}
    (hk₀ : 1 ≤ k) (hk : k ≤ S.card) :
    ((uniformNestChoice S k).prod (uniformNestChoice S k)).real
      {J : Finset α × Finset α | (J.1 ∩ J.2).Nonempty} ≤ (k:ℝ)^2 / S.card := by
  let ν := uniformNestChoice S k
  letI : IsProbabilityMeasure ν := uniformNestChoice_probability S k hk
  let μ := ν.prod ν
  let good : Set (Finset α) := ↑(S.powersetCard k)
  let F (x : α) := {J : Finset α × Finset α | x ∈ J.1 ∧ x ∈ J.2}
  have hgood : ν good = 1 := by
    have heq : good = {J : Finset α | J ⊆ S ∧ J.card = k} := by ext J; simp [good]
    rw [heq]
    exact uniformNestChoice_admissible S k hk
  have hmass : μ (good ×ˢ good) = 1 := by simp [μ, Measure.prod_prod, hgood]
  have hnull : μ.real (good ×ˢ good)ᶜ = 0 := by
    rw [Measure.real, measure_compl ((S.powersetCard k).finite_toSet.measurableSet.prod
      (S.powersetCard k).finite_toSet.measurableSet) (measure_ne_top _ _), hmass, measure_univ,
      tsub_self, ENNReal.toReal_zero]
  have hcover : {J : Finset α × Finset α | (J.1 ∩ J.2).Nonempty} ⊆
      (⋃ x ∈ S, F x) ∪ (good ×ˢ good)ᶜ := by
    rintro ⟨J, J'⟩ ⟨x, hx⟩
    obtain ⟨hxJ, hxJ'⟩ := Finset.mem_inter.mp hx
    by_cases hg : (J, J') ∈ good ×ˢ good
    · have hxS := (Finset.mem_powersetCard.mp hg.1).1 hxJ
      exact Or.inl (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxS, ⟨hxJ, hxJ'⟩⟩⟩)
    · exact Or.inr hg
  have hS : (S.card:ℝ) ≠ 0 := by exact_mod_cast (show S.card ≠ 0 by omega)
  change μ.real _ ≤ _
  calc
    _ ≤ μ.real ((⋃ x ∈ S, F x) ∪ (good ×ˢ good)ᶜ) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (⋃ x ∈ S, F x) + μ.real (good ×ˢ good)ᶜ := measureReal_union_le _ _
    _ = μ.real (⋃ x ∈ S, F x) := by rw [hnull, add_zero]
    _ ≤ ∑ x ∈ S, μ.real (F x) := measureReal_biUnion_finset_le _ _
    _ = _ := by
      calc
        _ = ∑ _x ∈ S, ((k:ℝ)/S.card)^2 :=
          Finset.sum_congr rfl (fun _ hx => initial_nest_joint_membership_probability S hk₀ hk hx hx)
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp [hS] <;> ring

end NearCritical.Section10
