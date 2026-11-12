module

public import NearCritical.SlabTubeChartLaw
public import NearCritical.SlabTubeChart

/-! The Section 9 origin offspring bound transfers to the slab edge block
with the parent at either endpoint. -/
@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Section10
open scoped Classical

theorem slab_chart_offspring_failure_eq {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (e : boxBonds (centeredBox 2 R)) (rev : Bool)
    (a s : I) (Q₁ F₁ Q₃ F₃ S : Finset (Vertex d))
    (cand : Finset (Finset (Vertex d))) (patch : Finset (Vertex d) → Finset (Vertex d)) (N : ℕ)
    (hA : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) :
    let i := Fin.castLE hd e.1.2
    let M := section9FiniteMiddle i n
    let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
    let V := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
    let offspring := slabStepOffspring M L V Q₁ F₁ Q₃ F₃ S cand patch
    (rsν d n A R a s (Sum.inr e)).real
      {y | ¬ N ≤ (offspring (pullbackLayerPair (slabChartBond hd n e.1 rev)
        (slabTubePair n A R e y))).card} =
    ((percolation d a).prod (percolation d s)).real {z | ¬ N ≤ (offspring z).card} := by
  intro i M L V offspring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let T := sprinklingTube i n (-(5:ℝ)/8) (5/8)
  have hL : (L : Set (Vertex d)) ⊆ T := by
    intro x hx
    exact sprinklingLeftTube_subset i hnR
      ((mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) x).1 hx)
  have hV : (V : Set (Vertex d)) ⊆ T := by
    intro x hx
    exact sprinklingRightTube_subset i hnR
      ((mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) x).1 hx)
  have hM : (M : Set (Vertex d)) ⊆ T := by
    intro x hx
    change x ∈ section9FiniteMiddle i n at hx
    rw [section9FiniteMiddle_eq_inter] at hx
    exact hL (Finset.mem_inter.mp hx).1
  have hB {U : Finset (Vertex d)} (hU : (U : Set (Vertex d)) ⊆ T)
      {b : Bond d} (hb : b ∈ internalBondSet U) :
      bondIn (slabTube n e.1.1 e.1.2) (slabChartBond hd n e.1 rev b) := by
    obtain ⟨h₁,h₂⟩ := (mem_internalBondSet U b).mp hb
    exact slabChartBond_mem_tube hd n e.1 rev b ⟨hU h₁,hU h₂⟩
  apply congrArg ENNReal.toReal
  refine slab_tubeBlock_chart_prob_eq n R A e a s (slabChartBond hd n e.1 rev)
    (slabChartBond_injective hd n e.1 rev) (stepReadSet M L V Q₁ F₁ Q₃ F₃) ?_
    (fun z => ¬ N ≤ (offspring z).card)
    ((slabStepOffspring_readsOnly M L V Q₁ F₁ Q₃ F₃ S cand patch).comp
      (fun children => ¬ N ≤ children.card))
  intro k hk
  suffices hb : bondIn (slabTube n e.1.1 e.1.2) (slabChartBond hd n e.1 rev k.2) from
    ⟨hA _ hb, hb⟩
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact hB hL (Finset.mem_sdiff.mp hb).1
      · exact hB hV (Finset.mem_sdiff.mp hb).1
    · exact hB hM hb
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    exact hB hM hb

end NearCritical
