module
public import NearCritical.Section8HeartCovariance
public import NearCritical.HalfSpaceLastVisit

/-! Finite-plane BK decomposition retaining the upper cutoff in the domain.
This prevents the full-halfspace/slab substitution in the Appendix cube proof. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Last intermediate-plane split for an actual finite domain. The second
factor retains Q, in particular every upper height constraint imposed by Q. -/
theorem finite_connection_last_plane_bk {d : ℕ} (p : unitInterval)
    (Q : Finset (Vertex d)) (x y : Vertex d) (i : Fin d) (l : ℤ)
    (hx : x i ≤ l) (hy : l ≤ y i) :
    (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤
      ∑ u ∈ Q.filter (fun u => u i = l),
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {u}) *
        (percolation d p).real
          (connectionToSetEvent ((Q : Set (Vertex d)) ∩ {z | l ≤ z i}) u {y}) := by
  let M := Q.filter (fun u => u i = l)
  let A := fun u => connectionToSetEvent (Q : Set (Vertex d)) x {u}
  let B := fun u => connectionToSetEvent ((Q : Set (Vertex d)) ∩ {z | l ≤ z i}) u {y}
  let E := fun u => {ω : Configuration d | DisjointOccurrence (A u) (B u) ω}
  have hsub : connectionToSetEvent (Q : Set (Vertex d)) x {y} ⊆ ⋃ u ∈ M, E u := by
    intro ω hω
    obtain ⟨u,hul,hdis⟩ := connectionToSet_last_height_split (Q : Set (Vertex d)) {y} x i l hx
      (fun z hz => by have hzy : z = y := hz; simpa only [hzy] using hy) hω
    have huQ : u ∈ Q := by
      obtain ⟨F,H,_hF,_hH,_hd,hA,_hB⟩ := hdis
      obtain ⟨_hx,z,hz,hzQ,_hp⟩ := hA ω (fun _ _ => rfl)
      have hzu : z = u := hz
      simpa only [hzu, Finset.mem_coe] using hzQ
    exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨huQ,hul⟩,hdis⟩⟩
  calc
    _ ≤ (percolation d p).real (⋃ u ∈ M, E u) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ u ∈ M, (percolation d p).real (E u) := measureReal_biUnion_finset_le M E
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u _hu
      exact connectionToSet_bk p (Q : Set (Vertex d))
        ((Q : Set (Vertex d)) ∩ {z | l ≤ z i}) x u {u} {y}

end NearCritical.Section8
