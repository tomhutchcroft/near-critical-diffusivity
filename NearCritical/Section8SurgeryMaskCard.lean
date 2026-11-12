module
public import NearCritical.Section8UniqueExtensionProbability

/-! Actual surgery-mask cardinality and the uniform segment-size coefficient. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

private def surgery_predecessor_bond {d : ℕ} (e : Bond d) : Bond d :=
  (Function.update e.1 e.2 (e.1 e.2 - 1),e.2)

private theorem surgery_predecessor_tip {d : ℕ} (b : Bond d) :
    surgery_predecessor_bond (bondTip b,b.2) = b := by
  apply Prod.ext
  · funext j
    by_cases hj : j = b.2
    · subst j
      simp only [surgery_predecessor_bond,bondTip,Function.update_self]
      omega
    · simp [surgery_predecessor_bond,bondTip,hj]
  · rfl

/-- The actual available-bond mask touching I has at most 2d bonds per
vertex of I, including both physical endpoint orientations. -/
theorem section8_surgery_mask_card_le {d : ℕ} (T Q F I : Finset (Vertex d)) :
    (sprinklingClusterFiberMask T Q F I).card ≤ 2*d*I.card := by
  let O : Finset (Bond d) := I ×ˢ (Finset.univ : Finset (Fin d))
  let N : Finset (Bond d) := O.image surgery_predecessor_bond
  have hsub : sprinklingClusterFiberMask T Q F I ⊆ O ∪ N := by
    intro b hb
    rcases (Finset.mem_filter.mp hb).2 with hbase | htip
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr ⟨hbase,Finset.mem_univ _⟩))
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨(bondTip b,b.2),
        Finset.mem_product.mpr ⟨htip,Finset.mem_univ _⟩,surgery_predecessor_tip b⟩
  calc
    _ ≤ (O ∪ N).card := Finset.card_le_card hsub
    _ ≤ O.card+N.card := Finset.card_union_le O N
    _ ≤ O.card+O.card := Nat.add_le_add_left (Finset.card_image_le) O.card
    _ = _ := by
      simp only [O,Finset.card_product,Finset.card_univ,Fintype.card_fin]
      ring

private theorem surgery_uniform_coefficient_le {d : ℕ} (p : unitInterval)
    (T Q F I : Finset (Vertex d)) (r : ℕ) (hIcard : I.card ≤ r+1) :
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) ≤
      (min (p : ℝ) (1-(p : ℝ)))^(sprinklingClusterFiberMask T Q F I).card := by
  have hm0 : 0 ≤ min (p : ℝ) (1-(p : ℝ)) :=
    le_min p.property.1 (sub_nonneg.mpr p.property.2)
  have hm1 : min (p : ℝ) (1-(p : ℝ)) ≤ 1 := (min_le_left _ _).trans p.property.2
  exact pow_le_pow_of_le_one hm0 hm1
    ((section8_surgery_mask_card_le T Q F I).trans (Nat.mul_le_mul_left (2*d) hIcard))

/-- The ordinary surgery comparison has a coefficient depending only on d,
r and p, once the structural segment-size bound I.card≤r+1 is supplied. -/
theorem section8_unique_extension_uniform_surgery_probability {d : ℕ} (p : unitInterval)
    (T Q F I W : Finset (Vertex d)) (x x' z : Vertex d) (r : ℕ)
    (hIcard : I.card ≤ r+1)
    (hIT : I ⊆ T) (hx : x ∈ I) (hx' : x' ∈ I) (hz : z ∉ I)
    (hIW : ∀ y ∈ I, y ∈ W → y = x)
    (hconnected : ∀ u ∈ I,
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x u) :
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) *
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W x') ≤
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) :=
  (mul_le_mul_of_nonneg_right (surgery_uniform_coefficient_le p T Q F I r hIcard)
    measureReal_nonneg).trans
    (section8_unique_extension_surgery_probability p T Q F I W x x' z
      hIT hx hx' hz hIW hconnected)

/-- The same uniform coefficient holds under the actual positive two-heart
reveal law, with all surgery guards retained and freshness already proved. -/
theorem section8_unique_extension_uniform_surgery_revealed_probability {d : ℕ}
    (p : unitInterval) (T Q F I W H Q₃ H₃ F₃ : Finset (Vertex d))
    (x x' z : Vertex d) (r : ℕ) (hIcard : I.card ≤ r+1)
    (hH : H ⊆ Q) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q H Q₃ H₃ F F₃) ≠ 0)
    (hTQ₃ : Disjoint T Q₃)
    (hIT : I ⊆ T) (hx : x ∈ I) (hx' : x' ∈ I) (hz : z ∉ I)
    (hIW : ∀ y ∈ I, y ∈ W → y = x)
    (hconnected : ∀ u ∈ I,
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x u) :
    let ν := section9RevealedLaw p Q H Q₃ H₃ F F₃
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) *
      ν.real (section9AvoidanceEvent T T Q F {z} W x') ≤
      ν.real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) := by
  intro ν
  exact (mul_le_mul_of_nonneg_right (surgery_uniform_coefficient_le p T Q F I r hIcard)
    measureReal_nonneg).trans
    (section8_unique_extension_surgery_revealed_probability p T Q F I W H Q₃ H₃ F₃
      x x' z hH hH₃ hpos hTQ₃ hIT hx hx' hz hIW hconnected)

end NearCritical
