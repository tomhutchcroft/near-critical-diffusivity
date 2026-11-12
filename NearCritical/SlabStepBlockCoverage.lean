module

public import NearCritical.SlabTubeBlockLaw
public import NearCritical.Section10TubeArithmetic
public import NearCritical.Section9MiddleGeometry
public import NearCritical.Section10UnconditionalStep

/-! The Section 9 step in a slab tube can be evaluated with its two-copy tube
block. The critical part of the block partitions the tube bonds according to
whether they lie in a cube. The sprinkle part contains all tube bonds. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Section10
open scoped Classical

/-- The full Section 9 tube has exactly the coordinates of the slab tube. -/
theorem mem_slabTube_iff_mem_section9Tube {d : ℕ} (hd : 2 ≤ d) (n : ℕ)
    (u : Vertex 2) (i : Fin 2) (x : Vertex d) :
    x ∈ slabTube n u i ↔ x ∈ translateSites (coarseShift n u)
      (section9FiniteTube (Fin.castLE hd i) n (-(5 : ℝ)/8) (5/8)) := by
  rw [mem_stepTube _ _ _ _ _ _ (by norm_num) (by norm_num)]
  constructor
  · intro hx
    have h := hx.1 (Fin.castLE hd i) rfl
    refine ⟨by linarith [h.1], by linarith [h.2], ?_⟩
    intro j hj
    have h := abs_lt.mp (hx.2 j (fun h => hj (Fin.ext h)))
    constructor <;> linarith [h.1, h.2]
  · rintro ⟨hl, hu, ht⟩
    constructor
    · intro j hj
      have he : j = Fin.castLE hd i := Fin.ext hj
      subst j
      exact ⟨by linarith, by linarith⟩
    · intro j hj
      have h := ht j (fun h => hj (congrArg Fin.val h))
      apply abs_lt.mpr
      constructor <;> linarith [h.1, h.2]

/-- The left, right and middle regions of the positive step lie in the
single slab tube for its coarse edge. -/
theorem slab_stepRegions_subset {d : ℕ} (hd : 2 ≤ d) (n : ℕ)
    (u : Vertex 2) (i : Fin 2) :
    let c : Vertex d := coarseShift n u
    let j := Fin.castLE hd i
    (stepL n c j : Set (Vertex d)) ⊆ slabTube n u i ∧
      (stepR n c j : Set (Vertex d)) ⊆ slabTube n u i ∧
      (stepMid n c j : Set (Vertex d)) ⊆ slabTube n u i := by
  intro c j
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : (stepL n c j : Set (Vertex d)) ⊆ slabTube n u i := by
    intro x hx
    apply (mem_slabTube_iff_mem_section9Tube hd n u i x).2
    change x ∈ stepL n c j at hx
    rw [stepL, mem_stepTube _ _ _ _ _ _ (by norm_num) (by norm_num)] at hx
    rw [mem_stepTube _ _ _ _ _ _ (by norm_num) (by norm_num)]
    exact ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
  refine ⟨hL, ?_, ?_⟩
  · intro x hx
    apply (mem_slabTube_iff_mem_section9Tube hd n u i x).2
    change x ∈ stepR n c j at hx
    rw [stepR, mem_stepTube _ _ _ _ _ _ (by norm_num) (by norm_num)] at hx
    rw [mem_stepTube _ _ _ _ _ _ (by norm_num) (by norm_num)]
    exact ⟨by linarith [hx.1], hx.2.1, hx.2.2⟩
  · intro x hx
    apply hL
    change x ∈ stepMid n c j at hx
    rw [stepMid, section9FiniteMiddle_eq_inter] at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (Finset.mem_inter.mp hy).1

/-- A step event has the same probability on a slab tube block as under the
product law, when its three finite regions lie in the tube. -/
theorem slab_stepBlock_prob_eq_prod {d : ℕ} (n : ℕ) (A : Finset (Bond d))
    (Bx : Finset (Vertex 2)) (e : boxBonds Bx) (a s : I)
    (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hM : (M : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hL : (L : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hR : (R : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hA : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A)
    (P : Configuration d × Configuration d → Prop)
    (hP : ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃) P) :
    let B₁ := slabSprinkleBlocks n A Bx (Sum.inr e)
    let B₂ := slabStripBlocks n A Bx (Sum.inr e)
    ((Measure.pi fun k : B₁ => sprinkleLaw a s (k : Bond d × Bool)).prod
      (Measure.pi fun k : B₂ => sprinkleLaw a s (k : Bond d × Bool)))
      {y | P (criticalLayer (tubeLayers B₁ B₂ y), sprinkleLayer (tubeLayers B₁ B₂ y))} =
    ((percolation d a).prod (percolation d s)) {z | P z} := by
  intro B₁ B₂
  let Tc := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃ ∪
    internalBondSet M
  have hb {U : Finset (Vertex d)} (hU : (U : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
      {b : Bond d} (h : b ∈ internalBondSet U) : bondIn (slabTube n e.1.1 e.1.2) b := by
    obtain ⟨h₁, h₂⟩ := (mem_internalBondSet U b).mp h
    exact ⟨hU h₁, hU h₂⟩
  have hTc (b : Bond d) (h : b ∈ Tc) : bondIn (slabTube n e.1.1 e.1.2) b := by
    change b ∈ (_ ∪ _) ∪ _ at h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hb hL (Finset.mem_sdiff.mp h).1
      · exact hb hR (Finset.mem_sdiff.mp h).1
    · exact hb hM h
  refine tubeBlock_prob_eq_prod a s B₁ B₂ {z | P z} hP.measurableSet Tc (internalBondSet M)
    (fun b h => ?_) (fun b h => ?_) (fun z z' hc hs => ?_)
  · have hT := hTc b h
    by_cases hC : ∃ v ∈ Bx, bondIn (slabCube n v) b
    · right
      simp [B₂, slabStripBlocks, hA b hT, hT, hC]
    · left
      have hC' : ∀ v ∈ Bx, ¬ bondIn (slabCube n v) b :=
        fun v hv hb => hC ⟨v, hv, hb⟩
      simpa [B₁, slabSprinkleBlocks, hA b hT, hT] using hC'
  · have hT := hb hM h
    constructor
    · simp [B₁, slabSprinkleBlocks, hA b hT, hT]
    · simp [B₂, slabStripBlocks]
  · change P z ↔ P z'
    apply Iff.of_eq
    apply hP
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
      exact hc b hb
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
      exact hs b hb

end NearCritical
