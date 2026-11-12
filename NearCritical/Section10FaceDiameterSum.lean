module

public import NearCritical.SpanningBoundaryDiameter
public import NearCritical.Section10BoxDistanceMoment

/-! The face diameter of a cluster is at most a double sum of pairwise
distances over its boundary points.

`spanningFaceDiameter_le_sum`: if every face lies in `B`, then

  `spanningFaceDiameter G C faces <= sum_{u in C ∩ B} sum_{v in C ∩ B} dist_G(u, v)`.

This is the "maximum relaxed to a sum" step for the diameter condition (3) of
def.spanning.z; with `restricted_dist_integral_le` it reduces the expected
diameter of a cluster to sums of two-point functions inside the cube.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem spanningFaceDiameter_le_sum {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph (Vertex d)) (C B : Finset (Vertex d)) (faces : ι → Finset (Vertex d))
    (hB : ∀ i, faces i ⊆ B) :
    spanningFaceDiameter G C faces ≤ ∑ u ∈ C ∩ B, ∑ v ∈ C ∩ B, G.dist u v := by
  unfold spanningFaceDiameter
  refine Finset.sup_le (fun p _ => Finset.sup_le (fun xy hxy => ?_))
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
  have hu : xy.1 ∈ C ∩ B :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1).1, hB p.1 (Finset.mem_inter.mp h1).2⟩
  have hv : xy.2 ∈ C ∩ B :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h2).1, hB p.2 (Finset.mem_inter.mp h2).2⟩
  calc G.dist xy.1 xy.2 ≤ ∑ v ∈ C ∩ B, G.dist xy.1 v :=
        Finset.single_le_sum (f := fun v => G.dist xy.1 v) (fun _ _ => Nat.zero_le _) hv
    _ ≤ ∑ u ∈ C ∩ B, ∑ v ∈ C ∩ B, G.dist u v :=
        Finset.single_le_sum (f := fun u => ∑ v ∈ C ∩ B, G.dist u v)
          (fun _ _ => Nat.zero_le _) hu

end NearCritical.Section10
