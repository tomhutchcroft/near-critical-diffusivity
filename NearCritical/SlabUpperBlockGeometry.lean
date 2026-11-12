module

public import NearCritical.SlabUpperSprinkleCoupling

/-! Coarse cube/tube arrangement for prop.slab.upper and disjointness of the
sprinkle blocks (input (i) of the slab interface).

Coarse site `v ∈ ℤ²` ↦ cube `Λ_n(2n v)` (open, side `n`, the source/`sprinklingEndCube`
shape); coarse bond `(u, i)` ↦ tube `2n u + n e_i + (-5n/8, 5n/8) × (-3n/8, 3n/8)^{d-1}`
(the source `T₁₂₃`/`sprinklingTube i n (-5/8) (5/8)` shape). Proved: distinct
cubes are disjoint, distinct tubes are disjoint (source: "the tubes of different
pairs of neighbours are disjoint"), hence `slabSprinkleBlocks` — base bits of cube
bonds, sprinkle bits of tube bonds and base bits of tube bonds outside all box
cubes — are pairwise disjoint, for any finite ambient bond set `A`. -/

@[expose] public section
noncomputable section

namespace NearCritical

open Finset
open scoped Classical

variable {d : ℕ}

/-- Fine-lattice position of coarse site `v`. -/
def coarseShift (n : ℕ) (v : Vertex 2) : Vertex d :=
  fun j => if h : j.val < 2 then 2 * (n : ℤ) * v ⟨j.val, h⟩ else 0

lemma coarseShift_apply (hd : 2 ≤ d) (n : ℕ) (v : Vertex 2) (c : Fin 2) :
    coarseShift (d := d) n v (Fin.castLE hd c) = 2 * (n : ℤ) * v c := by
  simp [coarseShift, c.2]

def slabCube (n : ℕ) (v : Vertex 2) : Set (Vertex d) :=
  {x | ∀ j, |((x j - coarseShift n v j : ℤ) : ℝ)| < (n : ℝ) / 2}

def slabTube (n : ℕ) (u : Vertex 2) (i : Fin 2) : Set (Vertex d) :=
  {x | (∀ j : Fin d, j.val = i.val →
      3 * (n : ℝ) / 8 < ((x j - coarseShift n u j : ℤ) : ℝ) ∧
        ((x j - coarseShift n u j : ℤ) : ℝ) < 13 * (n : ℝ) / 8) ∧
    (∀ j : Fin d, j.val ≠ i.val → |((x j - coarseShift n u j : ℤ) : ℝ)| < 3 * (n : ℝ) / 8)}

lemma int_sep {a b : ℤ} (h : a ≠ b) : a + 1 ≤ b ∨ b + 1 ≤ a := by omega

theorem slabCube_disjoint (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n) {v w : Vertex 2} (hvw : v ≠ w)
    {x : Vertex d} (hv : x ∈ slabCube n v) (hw : x ∈ slabCube n w) : False := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hvw
  have h1 := hv (Fin.castLE hd c)
  have h2 := hw (Fin.castLE hd c)
  rw [coarseShift_apply hd] at h1 h2
  push_cast at h1 h2
  rw [abs_lt] at h1 h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases int_sep hc with h | h
  · have : ((v c : ℤ) : ℝ) + 1 ≤ (w c : ℝ) := by exact_mod_cast h
    nlinarith
  · have : ((w c : ℤ) : ℝ) + 1 ≤ (v c : ℝ) := by exact_mod_cast h
    nlinarith

theorem slabTube_disjoint (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n) {u w : Vertex 2} {i i' : Fin 2}
    (hne : (u, i) ≠ (w, i')) {x : Vertex d} (hu : x ∈ slabTube n u i)
    (hw : x ∈ slabTube n w i') : False := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hii : i = i'
  · subst hii
    have huw : u ≠ w := fun h => hne (by rw [h])
    obtain ⟨c, hc⟩ := Function.ne_iff.1 huw
    by_cases hci : c = i
    · subst hci
      have h1 := hu.1 (Fin.castLE hd c) rfl
      have h2 := hw.1 (Fin.castLE hd c) rfl
      rw [coarseShift_apply hd] at h1 h2
      push_cast at h1 h2
      rcases int_sep hc with h | h
      · have : ((u c : ℤ) : ℝ) + 1 ≤ (w c : ℝ) := by exact_mod_cast h
        nlinarith
      · have : ((w c : ℤ) : ℝ) + 1 ≤ (u c : ℝ) := by exact_mod_cast h
        nlinarith
    · have hcv : (Fin.castLE hd c).val ≠ i.val := fun h => hci (Fin.ext h)
      have h1 := hu.2 (Fin.castLE hd c) hcv
      have h2 := hw.2 (Fin.castLE hd c) hcv
      rw [coarseShift_apply hd] at h1 h2
      push_cast at h1 h2
      rw [abs_lt] at h1 h2
      rcases int_sep hc with h | h
      · have : ((u c : ℤ) : ℝ) + 1 ≤ (w c : ℝ) := by exact_mod_cast h
        nlinarith
      · have : ((w c : ℤ) : ℝ) + 1 ≤ (u c : ℝ) := by exact_mod_cast h
        nlinarith
  · have hv' : (Fin.castLE hd i).val ≠ i'.val := fun h => hii (Fin.ext h)
    have h1 := hu.1 (Fin.castLE hd i) rfl
    have h2 := hw.2 (Fin.castLE hd i) hv'
    rw [coarseShift_apply hd] at h1 h2
    push_cast at h1 h2
    rw [abs_lt] at h2
    rcases le_or_gt (w i) (u i) with h | h
    · have : ((w i : ℤ) : ℝ) ≤ (u i : ℝ) := by exact_mod_cast h
      nlinarith
    · have h' : u i + 1 ≤ w i := h
      have : ((u i : ℤ) : ℝ) + 1 ≤ (w i : ℝ) := by exact_mod_cast h'
      nlinarith

/-- Bonds with both endpoints in `U`. -/
def bondIn (U : Set (Vertex d)) (e : Bond d) : Prop := e.1 ∈ U ∧ bondTip e ∈ U

/-- Source-faithful sprinkle blocks on the ℤ² box `Bx`, inside ambient bonds `A`. -/
def slabSprinkleBlocks (n : ℕ) (A : Finset (Bond d)) (Bx : Finset (Vertex 2)) :
    Bx ⊕ boxBonds Bx → Finset (Bond d × Bool)
  | .inl v => (A.filter (bondIn (slabCube n v.1))) ×ˢ {true}
  | .inr e =>
      (A.filter (bondIn (slabTube n e.1.1 e.1.2))) ×ˢ {false} ∪
      (A.filter (fun b => bondIn (slabTube n e.1.1 e.1.2) b ∧
        ∀ v ∈ Bx, ¬ bondIn (slabCube n v) b)) ×ˢ {true}

theorem slabSprinkleBlocks_disjoint (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n) (A : Finset (Bond d))
    (Bx : Finset (Vertex 2)) :
    Pairwise fun i j => Disjoint (slabSprinkleBlocks (d := d) n A Bx i)
      (slabSprinkleBlocks n A Bx j) := by
  rintro (v | e) (w | e') hij <;> rw [Finset.disjoint_left] <;>
    rintro ⟨b, t⟩ h1 h2 <;>
    simp only [slabSprinkleBlocks, Finset.mem_union, Finset.mem_product, Finset.mem_filter,
      Finset.mem_singleton] at h1 h2
  · have hvw : v.1 ≠ w.1 := fun h => hij (congrArg Sum.inl (Subtype.ext h))
    exact slabCube_disjoint hd hn hvw h1.1.2.1 h2.1.2.1
  · rcases h2 with ⟨-, ht⟩ | ⟨⟨-, -, hno⟩, -⟩
    · rw [h1.2] at ht; cases ht
    · exact hno v.1 v.2 h1.1.2
  · rcases h1 with ⟨-, ht⟩ | ⟨⟨-, -, hno⟩, -⟩
    · rw [h2.2] at ht; cases ht
    · exact hno w.1 w.2 h2.1.2
  · have hee : (e.1.1, e.1.2) ≠ (e'.1.1, e'.1.2) := by
      intro h
      apply hij
      congr 1
      exact Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    have tube1 : bondIn (slabTube n e.1.1 e.1.2) b := by
      rcases h1 with ⟨⟨-, hb⟩, -⟩ | ⟨⟨-, hb, -⟩, -⟩ <;> exact hb
    have tube2 : bondIn (slabTube n e'.1.1 e'.1.2) b := by
      rcases h2 with ⟨⟨-, hb⟩, -⟩ | ⟨⟨-, hb, -⟩, -⟩ <;> exact hb
    exact slabTube_disjoint hd hn hee tube1.1 tube2.1

end NearCritical
