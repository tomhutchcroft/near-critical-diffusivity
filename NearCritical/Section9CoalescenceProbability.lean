module

public import NearCritical.Section9CoalescenceBK

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Fixed-pivot contribution in the shared-right case, under the
original percolation law and with the right connection kept joint. -/
theorem section9_shared_right_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d) :
    let A := connectionToSetEvent (L : Set (Vertex d)) e.1 {x}
    let C := connectionToSetEvent (L : Set (Vertex d)) f.1 {y}
    let D := connectionToSetEvent (R : Set (Vertex d)) e.2 {f.2} ∩
      connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
    (percolation d p).real {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2} ≤
      (percolation d p).real A *
        ((percolation d p).real C * (percolation d p).real D) := by
  dsimp only
  let A := connectionToSetEvent (L : Set (Vertex d)) e.1 {x}
  let C := connectionToSetEvent (L : Set (Vertex d)) f.1 {y}
  let D := connectionToSetEvent (R : Set (Vertex d)) e.2 {f.2} ∩
    connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  let CD := {ω : Configuration d | DisjointOccurrence C D ω}
  have hA : BK.Increasing A := connectionToSetEvent_increasing _ _ _
  have hC : BK.Increasing C := connectionToSetEvent_increasing _ _ _
  have hD : BK.Increasing D := by
    intro ω θ h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  have hCD : BK.Increasing CD := by
    intro ω θ h hω
    obtain ⟨F, G, hFfin, hGfin, hdis, hF, hG, hCF, hDG⟩ :=
      BK.openDisjointOccurrence_of_disjointOccurrence hω
    exact BK.OpenDisjointOccurrence.to_disjointOccurrence
      ⟨F, G, hFfin, hGfin, hdis, (fun b hb => h b (hF b hb)),
        (fun b hb => h b (hG b hb)), hCF, hDG⟩ hC hD
  calc
    _ ≤ (percolation d p).real {ω | DisjointOccurrence A CD ω} :=
      measureReal_mono (fun ω h =>
        section9_shared_right_disjointOccurrence ω L R Q₁ F₁ Q₃ F₃ B x y e f
          h.1 h.2.1 h.2.2.1 h.2.2.2)
    _ ≤ (percolation d p).real A * (percolation d p).real CD :=
      percolation_bk d p A CD hA hCD
    _ ≤ _ := mul_le_mul_of_nonneg_left (percolation_bk d p C D hC hD) measureReal_nonneg

end NearCritical
