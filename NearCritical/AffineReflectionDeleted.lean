module
public import NearCritical.LatticeInversion
public import NearCritical.Section9AvoidanceCertificate

/-! Exact affine reflection of actual finite deleted clusters and avoidance. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Reflection in the midpoint c/2, as an involutive lattice equivalence. -/
def affineReflection {d : ℕ} (c : Vertex d) : Vertex d ≃ Vertex d where
  toFun v := c-v
  invFun v := c-v
  left_inv v := sub_sub_cancel c v
  right_inv v := sub_sub_cancel c v

/-- Configuration pullback for v↦c-v. Translation precedes inversion:
the reflected physical bond has base c-oldTip and tip c-oldBase. -/
def affineReflectConfiguration {d : ℕ} (c : Vertex d) (ω : Configuration d) : Configuration d :=
  invertConfiguration (translateConfiguration c ω)

private theorem affine_reflect_mem_image {d : ℕ} (c : Vertex d)
    (S : Finset (Vertex d)) (x : Vertex d) :
    affineReflection c x ∈ S.image (affineReflection c) ↔ x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    exact (affineReflection c).injective heq ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

private theorem affine_reflect_open_adj {d : ℕ} (c : Vertex d) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (affineReflectConfiguration c ω)).Adj x y ↔
      (openGraph ω).Adj (affineReflection c x) (affineReflection c y) := by
  simpa only [affineReflectConfiguration,affineReflection,Equiv.coe_fn_mk,sub_eq_add_neg] using
    (openGraph_invert_adj (translateConfiguration c ω) x y).trans
      (openGraph_translate_adj c ω (-x) (-y))

/-- Reflection transports the actual explored-edge deletion, along with all
finite domains. This is an isomorphism of the ambient-vertex graphs, including
isolated vertices outside the finite tube. -/
def affineReflectionDeletedGraphIso {d : ℕ} (c : Vertex d) (ω : Configuration d)
    (T Q F : Finset (Vertex d)) :
    sprinklingUnexploredGraph (affineReflectConfiguration c ω) T Q F ≃g
      sprinklingUnexploredGraph ω (T.image (affineReflection c))
        (Q.image (affineReflection c)) (F.image (affineReflection c)) where
  toEquiv := affineReflection c
  map_rel_iff' := by
    intro x y
    change ((openGraph ω).Adj (affineReflection c x) (affineReflection c y) ∧
      affineReflection c x ∈ T.image (affineReflection c) ∧
      affineReflection c y ∈ T.image (affineReflection c) ∧
      s(affineReflection c x,affineReflection c y) ∉
        exploredEdgeSet ((Q.image (affineReflection c) : Finset (Vertex d)) : Set (Vertex d))
          ((F.image (affineReflection c) : Finset (Vertex d)) : Set (Vertex d))) ↔
      ((openGraph (affineReflectConfiguration c ω)).Adj x y ∧ x ∈ T ∧ y ∈ T ∧
        s(x,y) ∉ exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))
    rw [← affine_reflect_open_adj c ω x y]
    simp only [pair_mem_exploredEdgeSet,Finset.mem_coe,affine_reflect_mem_image]

/-- The actual finite cluster transforms exactly. No root-in-tube hypothesis
is needed: finite tube membership remains part of the cluster definition. -/
theorem affineReflection_deletedCluster {d : ℕ} (c : Vertex d) (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (root : Vertex d) :
    (sprinklingUnexploredCluster (affineReflectConfiguration c ω) T Q F root).image
        (affineReflection c) =
      sprinklingUnexploredCluster ω (T.image (affineReflection c))
        (Q.image (affineReflection c)) (F.image (affineReflection c)) (affineReflection c root) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxT,hreach⟩ := (mem_sprinklingUnexploredCluster
      (affineReflectConfiguration c ω) T Q F root x).mp hx
    exact (mem_sprinklingUnexploredCluster ω (T.image (affineReflection c))
      (Q.image (affineReflection c)) (F.image (affineReflection c))
      (affineReflection c root) (affineReflection c x)).mpr
      ⟨Finset.mem_image.mpr ⟨x,hxT,rfl⟩,
        (affineReflectionDeletedGraphIso c ω T Q F).reachable_iff.mpr hreach⟩
  · intro hy
    obtain ⟨hyT,hreach⟩ := (mem_sprinklingUnexploredCluster ω
      (T.image (affineReflection c)) (Q.image (affineReflection c)) (F.image (affineReflection c))
      (affineReflection c root) y).mp hy
    obtain ⟨x,hxT,rfl⟩ := Finset.mem_image.mp hyT
    exact Finset.mem_image.mpr ⟨x,
      (mem_sprinklingUnexploredCluster (affineReflectConfiguration c ω) T Q F root x).mpr
        ⟨hxT,(affineReflectionDeletedGraphIso c ω T Q F).reachable_iff.mp hreach⟩,rfl⟩

private theorem affine_reflect_inter_nonempty {d : ℕ} (c : Vertex d)
    (S B : Finset (Vertex d)) :
    (S.image (affineReflection c) ∩ B.image (affineReflection c)).Nonempty ↔
      (S ∩ B).Nonempty := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hyS,hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hyS
    have hsB : s ∈ B := (affine_reflect_mem_image c B s).mp hyB
    exact ⟨s,Finset.mem_inter.mpr ⟨hs,hsB⟩⟩
  · rintro ⟨x,hx⟩
    obtain ⟨hxS,hxB⟩ := Finset.mem_inter.mp hx
    exact ⟨affineReflection c x,Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨x,hxS,rfl⟩,Finset.mem_image.mpr ⟨x,hxB,rfl⟩⟩⟩

/-- Reflection of the actual nonmonotone avoidance event. The positive
domain and the full larger nonhit tube are BOTH transformed, as are the
explored-edge deletion, target, forbidden set and root. -/
theorem affineReflection_avoidance_preimage {d : ℕ} (c : Vertex d)
    (D T Q F B W : Finset (Vertex d)) (root : Vertex d) :
    affineReflectConfiguration c ⁻¹' section9AvoidanceEvent D T Q F B W root =
      section9AvoidanceEvent (D.image (affineReflection c)) (T.image (affineReflection c))
        (Q.image (affineReflection c)) (F.image (affineReflection c))
        (B.image (affineReflection c)) (W.image (affineReflection c)) (affineReflection c root) := by
  ext ω
  have hD := affineReflection_deletedCluster c ω D Q F root
  have hT := affineReflection_deletedCluster c ω T Q F root
  have hpositive :
      (sprinklingUnexploredCluster (affineReflectConfiguration c ω) D Q F root ∩ B).Nonempty ↔
      (sprinklingUnexploredCluster ω (D.image (affineReflection c))
        (Q.image (affineReflection c)) (F.image (affineReflection c)) (affineReflection c root) ∩
        B.image (affineReflection c)).Nonempty := by
    rw [← hD]
    exact (affine_reflect_inter_nonempty c _ B).symm
  have hhit :
      (sprinklingUnexploredCluster (affineReflectConfiguration c ω) T Q F root ∩ W).Nonempty ↔
      (sprinklingUnexploredCluster ω (T.image (affineReflection c))
        (Q.image (affineReflection c)) (F.image (affineReflection c)) (affineReflection c root) ∩
        W.image (affineReflection c)).Nonempty := by
    rw [← hT]
    exact (affine_reflect_inter_nonempty c _ W).symm
  exact and_congr hpositive (not_congr hhit)

end NearCritical
