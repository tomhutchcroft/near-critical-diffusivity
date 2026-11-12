module

public import NearCritical.ConnectionToSet
public import NearCritical.LatticeShells
public import Mathlib.MeasureTheory.Measure.Continuity

/-! Actual finite-domain exhaustion for connection-to-set events, including
zero-length paths. Used to pass uniform finite-domain entropic bounds to H. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set

/-- A restricted walk remains a walk after intersecting its domain with any
set containing its entire support. -/
def restrictedWalk_inter_domain {d : ℕ} {ω : Configuration d} {S T : Set (Vertex d)}
    {x y : Vertex d} (w : (restrictedGraph ω S).Walk x y)
    (hT : ∀ z ∈ w.support, z ∈ T) : (restrictedGraph ω (S ∩ T)).Walk x y := by
  induction w with
  | nil => exact .nil
  | @cons x z y hadj w ih =>
    apply SimpleGraph.Walk.cons _ (ih (fun v hv => hT v (by simp [hv])))
    exact ⟨hadj.1, ⟨hadj.2.1, hT x (by simp)⟩, ⟨hadj.2.2, hT z (by simp)⟩⟩

lemma finiteDomain_connection_mono {d : ℕ} (S A : Set (Vertex d)) (x : Vertex d) :
    Monotone (fun R : ℕ => connectionToSetEvent
      (S ∩ (latticeSupCube d R : Set (Vertex d))) x A) := by
  intro m n hmn
  have hsub : S ∩ (latticeSupCube d m : Set (Vertex d)) ⊆
      S ∩ (latticeSupCube d n : Set (Vertex d)) := by
    rintro y ⟨hyS, hym⟩
    exact ⟨hyS, latticeSupCube_mono d hmn hym⟩
  exact connectionToSetEvent_mono hsub (Subset.refl A) x

/-- Every actual finite open path is contained in a finite counting cube.
No infinite-path or event approximation premise is assumed. -/
theorem connectionToSetEvent_eq_iUnion_finiteDomain {d : ℕ}
    (S A : Set (Vertex d)) (x : Vertex d) :
    connectionToSetEvent S x A = ⋃ R : ℕ,
      connectionToSetEvent (S ∩ (latticeSupCube d R : Set (Vertex d))) x A := by
  classical
  ext ω
  constructor
  · rintro ⟨hx, y, hy, hyS, hpath⟩
    obtain ⟨w⟩ := hpath
    obtain ⟨R, hR⟩ := exists_subset_latticeSupCube w.support.toFinset
    have hsupport : ∀ z ∈ w.support, z ∈ (latticeSupCube d R : Set (Vertex d)) := by
      intro z hz
      exact hR (List.mem_toFinset.mpr hz)
    refine Set.mem_iUnion.mpr ⟨R, ⟨hx, hsupport x (by simp)⟩, y, hy,
      ⟨hyS, hsupport y (by simp)⟩, ?_⟩
    exact (restrictedWalk_inter_domain w hsupport).reachable
  · intro h
    obtain ⟨R, hR⟩ := Set.mem_iUnion.mp h
    exact connectionToSetEvent_mono (fun y hy => hy.1) (Subset.refl A) x hR

/-- Uniform finite-domain real-probability bounds pass to the actual infinite
domain by continuity from below of the actual product measure. -/
theorem connectionToSet_probability_le_of_finiteDomain {d : ℕ} (p : unitInterval)
    (S A : Set (Vertex d)) (x : Vertex d) {B : ℝ}
    (hB : ∀ R : ℕ, (percolation d p).real
      (connectionToSetEvent (S ∩ (latticeSupCube d R : Set (Vertex d))) x A) ≤ B) :
    (percolation d p).real (connectionToSetEvent S x A) ≤ B := by
  have hB0 : 0 ≤ B := measureReal_nonneg.trans (hB 0)
  have he : percolation d p (connectionToSetEvent S x A) ≤ ENNReal.ofReal B := by
    rw [connectionToSetEvent_eq_iUnion_finiteDomain,
      (finiteDomain_connection_mono S A x).measure_iUnion]
    apply iSup_le
    intro R
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hB R)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [Measure.real, ENNReal.toReal_ofReal hB0] using h

end NearCritical
