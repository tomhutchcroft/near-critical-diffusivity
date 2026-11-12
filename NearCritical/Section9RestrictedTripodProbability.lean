module

public import NearCritical.Section9RestrictedTripod

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The joint connection probability is bounded by a finite sum over
target and branch vertices, with every arm in the original domain. -/
theorem restricted_joint_connection_probability_le {d : ℕ} (p : unitInterval)
    (R B : Finset (Vertex d)) (a b : Vertex d) :
    let D := (R : Set (Vertex d))
    let P := fun x y => (percolation d p).real (connectionToSetEvent D x {y})
    (percolation d p).real (connectionToSetEvent D a {b} ∩
      connectionToSetEvent D a (B : Set (Vertex d))) ≤
        ∑ z ∈ B, ∑ u ∈ R, P a u * (P u b * P z u) := by
  dsimp only
  let D := (R : Set (Vertex d))
  let A := fun u => connectionToSetEvent D a {u}
  let C := fun u => connectionToSetEvent D u {b}
  let K := fun z u => connectionToSetEvent D z {u}
  let J := fun z u => {ω : Configuration d | DisjointOccurrence (C u) (K z u) ω}
  let E := fun z u => {ω : Configuration d | DisjointOccurrence (A u) (J z u) ω}
  have hsub : connectionToSetEvent D a {b} ∩
      connectionToSetEvent D a (B : Set (Vertex d)) ⊆ ⋃ z ∈ B, ⋃ u ∈ R, E z u := by
    rintro ω ⟨⟨ha, v, hv, _, hab⟩, ⟨_, z, hz, _, haz⟩⟩
    have hvb : v = b := hv
    subst v
    obtain ⟨u, hu, hE⟩ := restricted_connection_tripod_occurrence D ha hab haz
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz,
      Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, hE⟩⟩⟩⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le B _).trans ?_
  apply Finset.sum_le_sum
  intro z _
  refine (measureReal_biUnion_finset_le R (E z)).trans ?_
  apply Finset.sum_le_sum
  intro u _
  have hA : BK.Increasing (A u) := connectionToSetEvent_increasing _ _ _
  have hC : BK.Increasing (C u) := connectionToSetEvent_increasing _ _ _
  have hK : BK.Increasing (K z u) := connectionToSetEvent_increasing _ _ _
  have hJ : BK.Increasing (J z u) := by
    intro ω θ h hω
    obtain ⟨F, G, hFfin, hGfin, hdis, hF, hG, hCF, hKG⟩ :=
      BK.openDisjointOccurrence_of_disjointOccurrence hω
    exact BK.OpenDisjointOccurrence.to_disjointOccurrence
      ⟨F, G, hFfin, hGfin, hdis, (fun e he => h e (hF e he)),
        (fun e he => h e (hG e he)), hCF, hKG⟩ hC hK
  exact (percolation_bk d p (A u) (J z u) hA hJ).trans
    (mul_le_mul_of_nonneg_left (percolation_bk d p (C u) (K z u) hC hK) measureReal_nonneg)

end NearCritical
