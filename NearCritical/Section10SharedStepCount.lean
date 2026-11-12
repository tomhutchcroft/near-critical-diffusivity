module

public import NearCritical.Section10PairMass
public import NearCritical.Section10RoutePhysicalEdges

@[expose] public section
namespace NearCritical.Section10
open scoped Classical

/-- An injective enumeration of physical steps charges each shared step
to one common unordered route edge. -/
theorem sharedStepCount_le_route_levels {A : Type*} (M n : ℕ) (X Y : ℕ → A)
    (edge : ℕ → Sym2 (ℕ × A))
    (hinj : Set.InjOn edge (Finset.range n : Set ℕ)) :
    sharedStepCount (fun t => decide
      (edge t ∈ routeUnorderedEdges M X ∩ routeUnorderedEdges M Y)) n ≤
        2 * (commonRouteLevels M X Y).card := by
  let C := routeUnorderedEdges M X ∩ routeUnorderedEdges M Y
  let S := (Finset.range n).filter (fun t => decide (edge t ∈ C) = true)
  have hS : Set.InjOn edge (S : Set ℕ) :=
    fun _ h₁ _ h₂ h => hinj (Finset.mem_filter.mp h₁).1 (Finset.mem_filter.mp h₂).1 h
  have hsub : S.image edge ⊆ C := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    exact of_decide_eq_true (Finset.mem_filter.mp ht).2
  calc
    _ = S.card := rfl
    _ = (S.image edge).card := (Finset.card_image_of_injOn hS).symm
    _ ≤ C.card := Finset.card_le_card hsub
    _ ≤ _ := common_unordered_route_edges_card_le_two_levels M X Y

/-- A route cannot traverse a physical edge twice in opposite
directions. Vertical steps increase the level, while horizontal steps
end at the distinguished site of their level. -/
theorem routeEdges_unordered_injective {A : Type*} (M : ℕ) (u : ℕ → A) :
    Set.InjOn (fun e : (ℕ × A) × (ℕ × A) => s(e.1, e.2))
      (routeEdges M u : Set ((ℕ × A) × (ℕ × A))) := by
  have hstep (a b : ℕ × A) (h : (a,b) ∈ routeEdges M u) :
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≠ u a.1 ∧ b.2 = u a.1) := by
    have hn := ((mem_routeEdges M u a b).mp h).2
    unfold routeNext at hn
    split_ifs at hn with hslot hlevel hprev
    · have hb := Option.some.inj hn
      subst b
      exact Or.inl (Nat.lt_succ_self _)
    · have hb := Option.some.inj hn
      subst b
      exact Or.inr ⟨rfl, hslot, rfl⟩
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd h
  rcases Sym2.eq_iff.mp h with ⟨hac,hbd⟩ | ⟨had,hbc⟩
  · exact Prod.ext hac hbd
  · change a = d at had
    change b = c at hbc
    subst d
    subst c
    rcases hstep a b hab with h | ⟨heq, ha, hb⟩
    · rcases hstep b a hcd with h' | ⟨heq, _, _⟩
      · exact (Nat.lt_asymm h h').elim
      · exact ((Nat.ne_of_lt h) heq.symm).elim
    · rcases hstep b a hcd with h' | ⟨_, hb', _⟩
      · exact ((Nat.ne_of_lt h') heq.symm).elim
      · exact (hb' (by simpa only [heq] using hb)).elim

/-- An enumeration of distinct directed edges of the first route gives
the physical shared-step bound without a separate unordered injectivity
hypothesis. -/
theorem sharedStepCount_le_route_levels_of_directed {A : Type*}
    (M n : ℕ) (u v : ℕ → A) (step : ℕ → (ℕ × A) × (ℕ × A))
    (hmem : ∀ t < n, step t ∈ routeEdges M u)
    (hinj : Set.InjOn step (Finset.range n : Set ℕ)) :
    sharedStepCount (fun t => decide
      (s((step t).1, (step t).2) ∈ routeUnorderedEdges M u ∩ routeUnorderedEdges M v))
      n ≤ 2 * (commonRouteLevels M u v).card := by
  apply sharedStepCount_le_route_levels
  intro i hi j hj hij
  apply hinj hi hj
  exact routeEdges_unordered_injective M u
    (hmem i (Finset.mem_range.mp hi)) (hmem j (Finset.mem_range.mp hj)) hij

/-- The pair-mass recurrence for a directed enumeration of the first
route, charged only at physical edges also used by the second route. -/
theorem pairRemainingMass_le_route_levels {A X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (S T : ℕ → X → X → Prop)
    (M n : ℕ) (u v : ℕ → A) (step : ℕ → (ℕ × A) × (ℕ × A))
    (hmem : ∀ t < n, step t ∈ routeEdges M u)
    (hinj : Set.InjOn step (Finset.range n : Set ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4)
    (hP : ∀ k < n, ∀ x y, 0 ≤ P k x y)
    (hS : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (S k) x)
    (hT : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (T k) x)
    (x : X) :
    pairRemainingMass P S T (fun t => decide
      (s((step t).1, (step t).2) ∈ routeUnorderedEdges M u ∩ routeUnorderedEdges M v))
      n x ≤ (1+ε/2)^(2*(commonRouteLevels M u v).card) :=
  pairRemainingMass_le_common_levels P S T _ hε hsmall n _ hP hS hT
    (sharedStepCount_le_route_levels_of_directed M n u v step hmem hinj) x

end NearCritical.Section10
