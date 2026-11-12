module

public import NearCritical.Section10SplitLowerCount

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- The strict transverse split interval can contain no lattice point.
In particular the simultaneous split crossing is impossible at scale one. -/
theorem crossAll_one_eq_empty {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) :
    crossAll 1 1 x = ∅ := by
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hji : j ≠ i := by
    intro h
    have h' := congrArg Fin.val h
    change 1 = 0 at h'
    omega
  ext ω
  simp only [Set.mem_empty_iff_false,iff_false]
  intro h
  obtain ⟨y,hy,_,_⟩ := h ((i,true),true)
  have hy' := (Finset.mem_filter.mp hy).1
  have hsplit := (Finset.mem_filter.mp hy').2.2 j hji
  change splitRange 1 true (y j) at hsplit
  norm_num [splitRange] at hsplit
  have hpos : 0 < y j := by exact_mod_cast (show (0:ℝ) < y j by linarith [hsplit.1])
  have hle : (1:ℝ) ≤ y j := by exact_mod_cast (show (1:ℤ) ≤ y j by omega)
  linarith [hsplit.2]

end NearCritical.Section10
