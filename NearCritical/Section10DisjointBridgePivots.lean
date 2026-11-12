module

public import NearCritical.Section9SprinklingCluster

/-! Deterministic pivot separation for (H2) of the pair estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

private theorem sprinkledPivotalPairs_mono_target {d : ℕ} (ω η : Configuration d)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d))
    {B T : Finset (Vertex d)} (hBT : B ⊆ T) :
    sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ A B ⊆
      sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ A T := by
  intro e he
  obtain ⟨heP, hadj, hl, hr, hs, ht, hd⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp he).1
  obtain ⟨y, hy⟩ := ht
  obtain ⟨hyC, hyB⟩ := Finset.mem_inter.mp hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨heP, hadj, hl, hr, hs, ⟨y, Finset.mem_inter.mpr ⟨hyC, hBT hyB⟩⟩, hd⟩,
    (Finset.mem_filter.mp he).2⟩

/-- The two target hits inside disjoint bridges use distinct physical bonds.
All four cross pairs of critical components are disjoint, including when
the source patches belong to opposite halves of the same cluster. -/
theorem disjoint_bridges_pivots_separate {d : ℕ} (ω η : Configuration d)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ B : Finset (Vertex d))
    (hB₁ : B₁ ⊆ B) (hB₂ : B₂ ⊆ B) (e f : Vertex d × Vertex d)
    (he : e ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ A₁ B₁)
    (hf : f ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ A₂ B₂)
    (hdis : Disjoint (section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ A₁ B)
      (section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ A₂ B)) :
    let U (g : Vertex d × Vertex d) := sprinklingUnexploredCluster ω L Q₁ F₁ g.1
    let V (g : Vertex d × Vertex d) := sprinklingUnexploredCluster ω R Q₃ F₃ g.2
    s(e.1, e.2) ≠ s(f.1, f.2) ∧ Disjoint (U e) (U f) ∧ Disjoint (U e) (V f) ∧
      Disjoint (V e) (U f) ∧ Disjoint (V e) (V f) := by
  intro U V
  have he' := sprinkledPivotalPairs_mono_target ω η P L R Q₁ F₁ Q₃ F₃ A₁ hB₁ he
  have hf' := sprinkledPivotalPairs_mono_target ω η P L R Q₁ F₁ Q₃ F₃ A₂ hB₂ hf
  have hsub (A : Finset (Vertex d)) (g : Vertex d × Vertex d)
      (hg : g ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ A B) :
      U g ∪ V g ⊆ section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ A B :=
    fun z hz => (mem_section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ A B z).mpr
      ⟨g, hg, Finset.mem_union.mp hz⟩
  have hd := hdis.mono (hsub A₁ e he') (hsub A₂ f hf')
  have hLL : Disjoint (U e) (U f) := hd.mono (Finset.subset_union_left) (Finset.subset_union_left)
  have hLR : Disjoint (U e) (V f) := hd.mono (Finset.subset_union_left) (Finset.subset_union_right)
  have hRL : Disjoint (V e) (U f) := hd.mono (Finset.subset_union_right) (Finset.subset_union_left)
  have hRR : Disjoint (V e) (V f) := hd.mono (Finset.subset_union_right) (Finset.subset_union_right)
  refine ⟨?_, hLL, hLR, hRL, hRR⟩
  intro h
  have heP := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have hfP := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
  have heL : e.1 ∈ U e := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ heP.2.1
  have hfL : f.1 ∈ U f := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hfP.2.1
  have hfR : f.2 ∈ V f := root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ hfP.2.2.1
  rcases Sym2.eq_iff.mp h with ⟨hfirst, _⟩ | ⟨hfirst, _⟩
  · exact Finset.disjoint_left.mp hLL heL (hfirst.symm ▸ hfL)
  · exact Finset.disjoint_left.mp hLR heL (hfirst.symm ▸ hfR)

end NearCritical.Section10
