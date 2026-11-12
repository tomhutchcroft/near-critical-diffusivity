module

public import NearCritical.Section10WeightedFreshUnion
public import NearCritical.Section10StepViewRevealLaw

/-! Step 3 of the pair estimate: sum the H3 row against the spread
occupation probabilities before the current tube is explored. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- The bridge from the independent sprinkle field reads the actual tube
block. Critical middle bonds, present in that block, are not needed here. -/
theorem rawBridge_readsOnly {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃)
      (fun z => section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B) := by
  intro z z' hz
  have hcrit : ∀ b ∈ (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) ∪
      internalBondSet M, z.1 b = z'.1 b := by
    intro b hb
    exact hz ((false, b) : LBond d)
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hspr : ∀ b ∈ internalBondSet M, z.2 b = z'.2 b := by
    intro b hb
    exact hz ((true, b) : LBond d) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  exact section9SprinklingCluster_eq_of_agree M L R Q₁ F₁ Q₃ F₃ A B _ _ _ _
    (fun b hb => hcrit b (Finset.mem_union_left _ (Finset.mem_union_left _ hb)))
    (fun b hb => hcrit b (Finset.mem_union_left _ (Finset.mem_union_right _ hb))) hspr

/-- The intersection event in the H3 row is local on the fresh tube. -/
theorem rawBridgeMeet_readsOnly {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃) (fun z =>
      (section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ X B ∩
        section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ Y B).Nonempty) := by
  intro z z' hz
  have hx := rawBridge_readsOnly M L R Q₁ F₁ Q₃ F₃ X B z z' hz
  have hy := rawBridge_readsOnly M L R Q₁ F₁ Q₃ F₃ Y B z z' hz
  dsimp only at hx hy ⊢
  rw [hx, hy]

/-- For distinct candidate clusters, the H3 row bound turns a per-pair
spread occupation estimate into a bound linear in the number of clusters.
This includes the actual full bridges of the two nests. -/
theorem spread_bridge_entry_integral_le {d : ℕ} {ι : Type*}
    (p q : unitInterval) (M L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (S : Finset ι) (X Y : ι → Finset (Vertex d))
    (R₀ : Finset (LBond d)) (hdis : Disjoint R₀ (stepReadSet M L R Q₁ F₁ Q₃ F₃))
    (G : Configuration d × Configuration d → ℝ)
    (hG : IsLocal R₀ G) (hG₀ : ∀ z, 0 ≤ G z)
    (J J' : Configuration d × Configuration d → Finset ι)
    (hJ : ReadsOnly R₀ J) (hJ' : ReadsOnly R₀ J')
    {a C : ℝ} (ha : 0 ≤ a)
    (hspread : ∀ x ∈ S, ∀ y ∈ S.erase x,
      (∫ z, ({z | x ∈ J z ∧ y ∈ J' z} : Set (Configuration d × Configuration d)).indicator G z
        ∂((percolation d p).prod (percolation d q))) ≤ a)
    (hrow : ∀ x ∈ S, (∑ y ∈ S.erase x,
      ((percolation d p).prod (percolation d q)).real {z |
        (section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (X x) B ∩
          section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty}) ≤ C) :
    let μ := (percolation d p).prod (percolation d q)
    (∫ z, ({z | ∃ x ∈ S, ∃ y ∈ S.erase x, x ∈ J z ∧ y ∈ J' z ∧
      (section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (X x) B ∩
        section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty} :
          Set (Configuration d × Configuration d)).indicator G z ∂μ) ≤ (S.card:ℝ) * (a * C) := by
  intro μ
  let I := S.sigma (fun x => S.erase x)
  let A (i : Σ _ : ι, ι) (z : Configuration d × Configuration d) := i.1 ∈ J z ∧ i.2 ∈ J' z
  let F (i : Σ _ : ι, ι) (z : Configuration d × Configuration d) :=
    (section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (X i.1) B ∩
      section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (Y i.2) B).Nonempty
  have hA (i : Σ _ : ι, ι) : ReadsOnly R₀ (A i) := by
    intro z z' hz
    simp only [A, hJ z z' hz, hJ' z z' hz]
  have heq : {z | ∃ i ∈ I, A i z ∧ F i z} = {z | ∃ x ∈ S, ∃ y ∈ S.erase x,
      x ∈ J z ∧ y ∈ J' z ∧ F ⟨x, y⟩ z} := by
    ext z
    constructor
    · rintro ⟨⟨x,y⟩, hxy, ⟨hx, hy⟩, hf⟩
      obtain ⟨hxS, hyS⟩ := Finset.mem_sigma.mp hxy
      exact ⟨x, hxS, y, hyS, hx, hy, hf⟩
    · rintro ⟨x, hxS, y, hyS, hx, hy, hf⟩
      exact ⟨⟨x,y⟩, Finset.mem_sigma.mpr ⟨hxS, hyS⟩, ⟨hx, hy⟩, hf⟩
  have h := weighted_fresh_union_le p q R₀ (stepReadSet M L R Q₁ F₁ Q₃ F₃) hdis
    I G hG hG₀ A F (fun i _ => hA i)
    (fun i _ => rawBridgeMeet_readsOnly M L R Q₁ F₁ Q₃ F₃ (X i.1) (Y i.2) B)
  dsimp only at h
  rw [heq] at h
  refine h.trans ?_
  change (∑ i ∈ S.sigma (fun x => S.erase x), (∫ z, {z | A i z}.indicator G z ∂μ) *
    μ.real {z | F i z}) ≤ _
  rw [Finset.sum_sigma]
  calc
    _ ≤ ∑ _x ∈ S, a * C := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        _ ≤ ∑ y ∈ S.erase x, a * μ.real {z | F ⟨x,y⟩ z} :=
          Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hspread x hx y hy) measureReal_nonneg
        _ = a * ∑ y ∈ S.erase x, μ.real {z | F ⟨x,y⟩ z} := by rw [Finset.mul_sum]
        _ ≤ a * C := mul_le_mul_of_nonneg_left (hrow x hx) ha
    _ = _ := by simp [nsmul_eq_mul]

end NearCritical.Section10
