module

public import NearCritical.ExternalFiniteSearch
public import OAI.Probability.CriticalPercolation.Exploration.State

/-!
Exact finite-bond exploration from openai/math4eaee875, specialized to actual
project bond subtypes. Original Apache license and hashes in third_party.
 Reachability below is in the explicitly defined
restricted labelled graph; equality with the project's domain-restricted
openGraph and the desired half-space event remain separate obligations.
-/
@[expose] public section
namespace NearCritical.External
open OAI.CriticalPercolation

/-- Restrict actual positive-coordinate bonds to a finite query domain. -/
def finiteBondSearchGraph {d : ℕ} (D : Finset (Bond d)) :
    BondGraph (Vertex d) D where
  ends e := s(e.val.1, bondTip e.val)

/-- The empty-read, singleton-root initial state of the upstream exact exposure. -/
def rootExposureState {d : ℕ} (D : Finset (Bond d)) (x : Vertex d) :
    ExactExposure.State (Vertex d) D := ⟨{x}, ∅⟩

/-- The exact exposure of a finite set of actual bonds never repeats a query. -/
theorem finite_exposure_no_repeats {d : ℕ} (D : Finset (Bond d))
    (x : Vertex d) (n : ℕ) (ω : Configuration d) :
    ((ExactExposure.compile (finiteBondSearchGraph D) n (rootExposureState D x)).reads
      (fun e => ω e.val)).Nodup := by
  exact SearchTree.reads_nodup _ _
    (ExactExposure.compile_valid (finiteBondSearchGraph D) n (rootExposureState D x)) _

/-- Every vertex reached by the finite-bond exposure is connected to the root
in the open labelled graph on those bonds. -/
theorem finite_exposure_sound {d : ℕ} (D : Finset (Bond d))
    (x : Vertex d) (n : ℕ) (ω : Configuration d) :
    ExactExposure.Sound (finiteBondSearchGraph D) {x}
      ((ExactExposure.compile (finiteBondSearchGraph D) n (rootExposureState D x)).run
        (fun e => ω e.val)) (fun e => ω e.val) := by
  have hc : ExactExposure.Consistent (finiteBondSearchGraph D)
      (rootExposureState D x) (fun e => ω e.val) := by
    simp [ExactExposure.Consistent, rootExposureState]
  have hs : ExactExposure.Sound (finiteBondSearchGraph D) {x}
      (rootExposureState D x) (fun e => ω e.val) := by
    intro v hv
    have hvx : v = x := Finset.mem_singleton.mp hv
    subst v
    exact ⟨x, Set.mem_singleton x, .refl x⟩
  exact (ExactExposure.compile_invariants (finiteBondSearchGraph D) {x} n
    (rootExposureState D x) (fun e => ω e.val) hc hs).2.1

/-- Query-domain cardinality is sufficient fuel to exhaust the finite exposure. -/
theorem finite_exposure_exhausted {d : ℕ} (D : Finset (Bond d))
    (x : Vertex d) (ω : Configuration d) :
    ¬ ∃ e, ExactExposure.eligible (finiteBondSearchGraph D)
      ((ExactExposure.compile (finiteBondSearchGraph D) D.card (rootExposureState D x)).run
        (fun e => ω e.val)) e := by
  apply ExactExposure.compile_exhausted
  simp [rootExposureState]

end NearCritical.External
