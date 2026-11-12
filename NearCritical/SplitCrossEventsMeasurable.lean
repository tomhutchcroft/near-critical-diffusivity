module

public import NearCritical.Section10SplitLowerCount
public import NearCritical.SpanningEmbeddedPath
public import NearCritical.ConnectionToSet

/-! Measurability of the split corridor crossing events. -/
@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

theorem measurableSet_crossSplit {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool)
    (R : ℕ) (x : Vertex d) : MeasurableSet (crossSplit t f pl R x) := by
  let S : Set (Vertex d) := splitCorridor t f pl R
  let A : Set (Vertex d) := splitTarget t f pl R
  have h : crossSplit t f pl R x = connectionToSetEvent S x A := by
    ext ω
    constructor
    · rintro ⟨y,hy,w,hw⟩
      exact ⟨hw x w.start_mem_support,y,hy,hw y w.end_mem_support,
        ⟨openWalkRestrictOfSupport S w hw⟩⟩
    · rintro ⟨hx,y,hy,_,⟨w⟩⟩
      have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1
      refine ⟨y,hy,w.mapLe hle,?_⟩
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      exact restrictedWalk_support w hx
  rw [h]
  exact measurableSet_connectionToSetEvent S x A

theorem measurableSet_crossAll {d : ℕ} (t R : ℕ) (x : Vertex d) :
    MeasurableSet (crossAll t R x) := by
  have h : crossAll t R x = ⋂ i : (Fin d × Bool) × Bool, crossSplit t i.1 i.2 R x := by
    ext ω
    simp [crossAll]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_crossSplit t i.1 i.2 R x

end NearCritical.Section10
