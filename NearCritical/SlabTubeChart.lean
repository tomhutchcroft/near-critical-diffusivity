module

public import NearCritical.SlabTubeEndCubes
public import NearCritical.SlabStepBlockCoverage
public import NearCritical.LatticeReflection

/-! Coordinates with the parent at the origin and the child in the positive
coordinate direction, for either orientation of a slab edge. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10

def slabChartVertex {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (x : Vertex d) : Vertex d :=
  if rev then coarseShift n (bondTip e) + reflVertex (Fin.castLE hd e.2) x
  else coarseShift n e.1 + x

def slabChartBond {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (b : Bond d) : Bond d :=
  if rev then translateBond (coarseShift n (bondTip e)) (reflBond (Fin.castLE hd e.2) b)
  else translateBond (coarseShift n e.1) b

theorem slabChartBond_injective {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool) :
    Function.Injective (slabChartBond hd n e rev) := by
  cases rev
  · exact (translateBond _).injective
  · exact (translateBond _).injective.comp (reflBond _).injective

/-- The vertex chart maps the full source tube into the physical slab tube. -/
theorem slabChartVertex_mem_tube {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (x : Vertex d) (hx : x ∈ sprinklingTube (Fin.castLE hd e.2) n (-(5:ℝ)/8) (5/8)) :
    slabChartVertex hd n e rev x ∈ slabTube n e.1 e.2 := by
  cases rev
  · apply (mem_slabTube_iff_mem_section9Tube hd n e.1 e.2 _).2
    exact Finset.mem_image_of_mem _
      ((mem_section9FiniteTube _ _ _ _ (by norm_num) (by norm_num) _).2 hx)
  · let i := Fin.castLE hd e.2
    change coarseShift n (bondTip e) + reflVertex i x ∈ slabTube n e.1 e.2
    rw [coarseShift_bondTip hd]
    constructor
    · intro j hj
      have he : j = i := Fin.ext hj
      subst j
      have hcoord : ((farCenter n (coarseShift n e.1) i + reflVertex i x) i -
          coarseShift n e.1 i : ℤ) = 2 * (n : ℤ) - x i := by
        simp only [Pi.add_apply, farCenter_apply_self, reflVertex, Function.update_self]
        ring
      rw [hcoord]
      push_cast
      constructor <;> linarith [hx.1, hx.2.1]
    · intro j hj
      have hne : j ≠ i := fun he => hj (congrArg (fun j : Fin d => j.val) he)
      have hcoord : ((farCenter n (coarseShift n e.1) i + reflVertex i x) j -
          coarseShift n e.1 j : ℤ) = x j := by
        simp [farCenter_apply_ne n (coarseShift n e.1) i hne, reflVertex, Function.update_of_ne hne]
      rw [hcoord, abs_lt]
      obtain ⟨hl, hu⟩ := hx.2.2 j hne
      constructor <;> linarith

/-- The chart's bond map sends internal source-tube bonds to internal
physical-tube bonds, including when a reflected bond reverses orientation. -/
theorem slabChartBond_mem_tube {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (b : Bond d) (hb : bondIn (sprinklingTube (Fin.castLE hd e.2) n (-(5:ℝ)/8) (5/8)) b) :
    bondIn (slabTube n e.1 e.2) (slabChartBond hd n e rev b) := by
  have h₁ := slabChartVertex_mem_tube hd n e rev b.1 hb.1
  have h₂ := slabChartVertex_mem_tube hd n e rev (bondTip b) hb.2
  cases rev
  · change bondIn (slabTube n e.1 e.2) (translateBond (coarseShift n e.1) b)
    refine ⟨h₁, ?_⟩
    rw [bondTip_translate]
    exact h₂
  · let i := Fin.castLE hd e.2
    let a : Vertex d := coarseShift n (bondTip e)
    change bondIn (slabTube n e.1 e.2) (translateBond a (reflBond i b))
    change a + reflVertex i b.1 ∈ slabTube n e.1 e.2 at h₁
    change a + reflVertex i (bondTip b) ∈ slabTube n e.1 e.2 at h₂
    by_cases h : b.2 = i
    · have hr : reflBond i b = (reflVertex i (bondTip b),i) := if_pos h
      rw [hr]
      refine ⟨h₂, ?_⟩
      rw [bondTip_translate, bondTip_reflBond_eq i b h]
      exact h₁
    · have hr : reflBond i b = (reflVertex i b.1,b.2) := if_neg h
      rw [hr]
      refine ⟨h₁, ?_⟩
      rw [bondTip_translate, bondTip_reflBond_ne i b h]
      exact h₂

/-- An open path in the pulled-back origin tube maps to a physical open
path in the slab tube. -/
theorem slabChart_reachable {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (ω : Configuration d) {x y : Vertex d}
    (h : (restrictedGraph (fun b => ω (slabChartBond hd n e rev b))
      (sprinklingTube (Fin.castLE hd e.2) n (-(5:ℝ)/8) (5/8))).Reachable x y) :
    (restrictedGraph ω (slabTube n e.1 e.2)).Reachable
      (slabChartVertex hd n e rev x) (slabChartVertex hd n e rev y) := by
  let f : restrictedGraph (fun b => ω (slabChartBond hd n e rev b))
        (sprinklingTube (Fin.castLE hd e.2) n (-(5:ℝ)/8) (5/8)) →g
      restrictedGraph ω (slabTube n e.1 e.2) := ⟨slabChartVertex hd n e rev, by
    intro u v huv
    obtain ⟨ho, hu, hv⟩ := huv
    refine ⟨?_, slabChartVertex_mem_tube hd n e rev u hu, slabChartVertex_mem_tube hd n e rev v hv⟩
    cases rev
    · exact (openGraph_translate_adj (coarseShift n e.1) ω u v).1 ho
    · let i := Fin.castLE hd e.2
      let a : Vertex d := coarseShift n (bondTip e)
      have h' := (openGraph_refl_adj i (translateConfiguration a ω) u v).1 ho
      exact (openGraph_translate_adj a ω (reflVertex i u) (reflVertex i v)).1 h'
  ⟩
  exact h.map f

end NearCritical
