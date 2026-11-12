module

public import NearCritical.SlabUpperBlockGeometry
public import NearCritical.Section10Section9Geometry

/-! Concrete index sets of the resampled slab sample.

* `mem_typicalCube_coarseShift`: the slab cube `slabCube n v` is the typical cube
  `typicalCube n (coarseShift n v)` of Section 10, so the pre-good test and the
  heart reveal of Section 10 apply to slab cubes; `internalBond_iff_bondIn`.
* `slabStripBlocks n A Bx`: the SECOND-copy index sets. A cube reads nothing
  from the second copy; a tube reads the critical-layer bits of its tube bonds
  that lie inside some cube of the box (its strips).
* `slabStripBlocks_disjoint`: they are pairwise disjoint.

The FIRST-copy index sets are the existing `slabSprinkleBlocks n A Bx` (cube:
critical bits of the cube; tube: sprinkle bits of the tube and critical bits of
tube bonds outside all cubes), pairwise disjoint by
`slabSprinkleBlocks_disjoint`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open Finset
open scoped Classical
open Section10

variable {d : ℕ}

lemma int_abs_lt_half_iff (a : ℤ) (n : ℕ) :
    |(a : ℝ)| < (n : ℝ) / 2 ↔
      -(((n - 1) / 2 : ℕ) : ℤ) ≤ a ∧ a ≤ (((n - 1) / 2 : ℕ) : ℤ) ∧ 0 < n := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    have r1 : ((-(n : ℤ) : ℤ) : ℝ) < ((2 * a : ℤ) : ℝ) := by push_cast; linarith
    have r2 : ((2 * a : ℤ) : ℝ) < ((n : ℤ) : ℝ) := by push_cast; linarith
    have h1' : -(n : ℤ) < 2 * a := by exact_mod_cast r1
    have h2' : 2 * a < (n : ℤ) := by exact_mod_cast r2
    refine ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, hn⟩
    have h1' : -(n : ℤ) < 2 * a := by omega
    have h2' : 2 * a < (n : ℤ) := by omega
    have r1 : ((-(n : ℤ) : ℤ) : ℝ) < ((2 * a : ℤ) : ℝ) := by exact_mod_cast h1'
    have r2 : ((2 * a : ℤ) : ℝ) < ((n : ℤ) : ℝ) := by exact_mod_cast h2'
    push_cast at r1 r2
    constructor <;> linarith

/-- A slab cube is a typical cube of Section 10. -/
theorem mem_typicalCube_coarseShift {n : ℕ} (hn : 0 < n) (v : Vertex 2) (x : Vertex d) :
    x ∈ typicalCube n (coarseShift (d := d) n v) ↔ x ∈ slabCube n v := by
  rw [mem_typicalCube_iff_int hn]
  constructor
  · intro h j
    exact (int_abs_lt_half_iff _ n).mpr ⟨(h j).1, (h j).2, hn⟩
  · intro h k
    have := (int_abs_lt_half_iff _ n).mp (h k)
    exact ⟨this.1, this.2.1⟩

theorem internalBond_iff_bondIn {n : ℕ} (hn : 0 < n) (v : Vertex 2) (e : Bond d) :
    e ∈ internalBondSet (typicalCube n (coarseShift (d := d) n v)) ↔ bondIn (slabCube n v) e := by
  rw [mem_internalBondSet, mem_typicalCube_coarseShift hn, mem_typicalCube_coarseShift hn]
  rfl

/-- Second-copy index sets: the strips of a tube. -/
def slabStripBlocks (n : ℕ) (A : Finset (Bond d)) (Bx : Finset (Vertex 2)) :
    Bx ⊕ boxBonds Bx → Finset (Bond d × Bool)
  | .inl _ => ∅
  | .inr e => (A.filter fun b => bondIn (slabTube n e.1.1 e.1.2) b ∧
      ∃ v ∈ Bx, bondIn (slabCube n v) b) ×ˢ {true}

theorem slabStripBlocks_disjoint (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n) (A : Finset (Bond d))
    (Bx : Finset (Vertex 2)) :
    Pairwise fun i j => Disjoint (slabStripBlocks (d := d) n A Bx i)
      (slabStripBlocks (d := d) n A Bx j) := by
  intro i j hij
  cases i with
  | inl v => exact Finset.disjoint_empty_left _
  | inr e =>
    cases j with
    | inl v => exact Finset.disjoint_empty_right _
    | inr e' =>
      have hdis : Disjoint (slabSprinkleBlocks (d := d) n A Bx (Sum.inr e))
          (slabSprinkleBlocks (d := d) n A Bx (Sum.inr e')) :=
        slabSprinkleBlocks_disjoint (d := d) hd hn A Bx hij
      change Disjoint (slabStripBlocks (d := d) n A Bx (Sum.inr e))
        (slabStripBlocks (d := d) n A Bx (Sum.inr e'))
      rw [Finset.disjoint_left] at hdis ⊢
      intro x hx hx'
      obtain ⟨b, c⟩ := x
      simp only [slabStripBlocks, Finset.mem_product, Finset.mem_filter] at hx hx'
      refine hdis (a := (b, false)) ?_ ?_
      · simp only [slabSprinkleBlocks]
        exact Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hx.1.1, hx.1.2.1⟩, Finset.mem_singleton_self _⟩)
      · simp only [slabSprinkleBlocks]
        exact Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hx'.1.1, hx'.1.2.1⟩, Finset.mem_singleton_self _⟩)

end NearCritical
