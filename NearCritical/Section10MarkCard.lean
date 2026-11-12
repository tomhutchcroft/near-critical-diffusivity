module

public import NearCritical.Section10RegularityLoss

/-! Cardinality of the marked boundary (`hcard` of `hloss_of_energy_moments`):
`|typMark t 0| <= 2d (2t)^(d-1)`. Source: `|boundary_1 Q| <~ n^(d-1)` in the
proof of prop.choice_c.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem signedCubeFace_card_le (d r : ℕ) (f : Fin d × Bool) :
    (signedCubeFace d r f).card ≤ (2 * r + 1) ^ (d - 1) := by
  have hT : (Fintype.piFinset
      (fun _ : {j : Fin d // j ≠ f.1} => Finset.Icc (-(r : ℤ)) (r : ℤ))).card =
      (2 * r + 1) ^ (d - 1) := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    have h1 : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
    have h2 : Fintype.card {j : Fin d // j ≠ f.1} = d - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp
    rw [h1, h2]
  rw [← hT]
  refine Finset.card_le_card_of_injOn (fun x j => x j.1) ?_ ?_
  · intro x hx
    unfold signedCubeFace at hx
    have hxb := mem_centeredBox.mp (Finset.mem_filter.mp hx).1
    exact Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr (hxb j.1)
  · intro x hx y hy hxy
    unfold signedCubeFace at hx hy
    have hx2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hy2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    funext j
    by_cases hj : j = f.1
    · rw [hj, hx2, hy2]
    · exact congrFun hxy ⟨j, hj⟩

theorem typMark_card_le {d : ℕ} (t : ℕ) (ht : 1 ≤ t) :
    ((typMark t (0 : Vertex d)).card : ℝ) ≤ (2 * (d : ℝ)) * (2 * (t : ℝ)) ^ (d - 1) := by
  have h1 : (typMark t (0 : Vertex d)).card ≤ (typicalBoundary t (0 : Vertex d)).card :=
    Finset.card_le_card (typMark_subset_boundary t 0)
  have h2 : (typicalBoundary t (0 : Vertex d)).card ≤
      ∑ _f : Fin d × Bool, (2 * t) ^ (d - 1) := by
    unfold typicalBoundary
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun f _ => ?_)
    rw [typicalFace_zero t ht f]
    exact (signedCubeFace_card_le d _ f).trans (Nat.pow_le_pow_left (by omega) _)
  have h3 : (typMark t (0 : Vertex d)).card ≤ (2 * d) * (2 * t) ^ (d - 1) := by
    refine (h1.trans h2).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, smul_eq_mul, mul_comm d 2]
  exact_mod_cast h3

end NearCritical.Section10
