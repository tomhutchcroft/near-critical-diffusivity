module

public import NearCritical.SlabChartCubes
public import NearCritical.Section10RevealPositivity

/-! A realized pair of heart unions remains realized in the parent chart,
which supplies the positive reveal event in the offspring estimate. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10 MeasureTheory
open scoped Classical

theorem slabChart_openAdj_iff {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (ω : Configuration d) (x y : Vertex d) :
    (openGraph (fun b => ω (slabChartBond hd n e rev b))).Adj x y ↔
      (openGraph ω).Adj (slabChartVertex hd n e rev x) (slabChartVertex hd n e rev y) := by
  cases rev
  · exact openGraph_translate_adj (coarseShift n e.1) ω x y
  · let i := Fin.castLE hd e.2
    let a : Vertex d := coarseShift n (bondTip e)
    exact (openGraph_refl_adj i (translateConfiguration a ω) x y).trans
      (openGraph_translate_adj a ω (reflVertex i x) (reflVertex i y))

def restrictedSlabChartIso {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (ω : Configuration d) (U : Finset (Vertex d)) :
    restrictedGraph (fun b => ω (slabChartBond hd n e rev b)) U ≃g
      restrictedGraph ω (U.image (slabChartVertex hd n e rev)) where
  toEquiv := slabChartEquiv hd n e rev
  map_rel_iff' := by
    intro x y
    simp only [restrictedGraph, slabChartEquiv_apply, ← slabChart_openAdj_iff,
      Finset.mem_coe, Finset.mem_image]
    have h (z : Vertex d) : (∃ w ∈ U, slabChartVertex hd n e rev w = slabChartVertex hd n e rev z) ↔ z ∈ U := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact (slabChartVertex_injective hd n e rev he) ▸ hw
      · exact fun hz => ⟨z,hz,rfl⟩
    rw [h,h]

theorem mem_finiteBoxCluster_slabChart_iff {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2)
    (rev : Bool) (ω : Configuration d) (Q : Finset (Vertex d)) (r x : Vertex d) :
    let f := slabChartVertex hd n e rev
    f x ∈ finiteBoxCluster ω (Q.image f) (f r) ↔
      x ∈ finiteBoxCluster (fun b => ω (slabChartBond hd n e rev b)) Q r := by
  intro f
  have hQ : f x ∈ Q.image f ↔ x ∈ Q := by
    constructor
    · intro h
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
      exact (slabChartVertex_injective hd n e rev he) ▸ hz
    · exact Finset.mem_image_of_mem f
  rw [mem_finiteBoxCluster, mem_finiteBoxCluster, hQ]
  apply and_congr_right
  intro _
  have h := (restrictedSlabChartIso hd n e rev ω Q).reachable_iff (u := r) (v := x)
  change (restrictedGraph ω (Q.image f : Set (Vertex d))).Reachable
      (slabChartEquiv hd n e rev r) (slabChartEquiv hd n e rev x) ↔ _ at h
  simpa only [slabChartEquiv_apply] using h

theorem mem_heartClusterUnion_slabChart_iff {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2)
    (rev : Bool) (ω : Configuration d) (Q H : Finset (Vertex d)) (x : Vertex d) :
    let f := slabChartVertex hd n e rev
    f x ∈ heartClusterUnion ω (Q.image f) (H.image f) ↔
      x ∈ heartClusterUnion (fun b => ω (slabChartBond hd n e rev b)) Q H := by
  intro f
  simp only [heartClusterUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hx⟩
    obtain ⟨r₀,hr₀,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨r₀,hr₀,(mem_finiteBoxCluster_slabChart_iff hd n e rev ω Q r₀ x).1 hx⟩
  · rintro ⟨r,hr,hx⟩
    exact ⟨f r,Finset.mem_image_of_mem f hr,(mem_finiteBoxCluster_slabChart_iff hd n e rev ω Q r x).2 hx⟩

end NearCritical
