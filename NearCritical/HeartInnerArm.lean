module

public import NearCritical.HeartMembershipBK
public import NearCritical.WaterCubeFaceArms
public import NearCritical.HalfSpaceSubcritical

/-! Actual inner-heart connection factor in NEW PxinfC. Both signed faces
use the already proved translation/inversion laws, retaining exact integer gaps. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

lemma innerEntryBoundary_subset_boundarySites {d : ℕ} (Q C : Finset (Vertex d)) :
    innerEntryBoundary Q C ⊆ boundarySites C := by
  intro v hv
  obtain ⟨hvC,u,_huQ,huC,huv⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvC,u,huC,huv.symm⟩

/-- An actual inner cube boundary vertex has some coordinate exactly positive or negative R. -/
lemma centeredBox_boundary_coordinate {d R : ℕ} {v : Vertex d}
    (hv : v ∈ boundarySites (centeredBox d R)) :
    ∃ i : Fin d, v i = (R:ℤ) ∨ v i = -(R:ℤ) := by
  obtain ⟨hvC,u,huC,hvu⟩ := Finset.mem_filter.mp hv
  have hout : ∃ i : Fin d, ¬ (-(R:ℤ) ≤ u i ∧ u i ≤ (R:ℤ)) := by
    simpa only [mem_centeredBox,not_forall] using huC
  obtain ⟨i,hi⟩ := hout
  have hvb := mem_centeredBox.mp hvC i
  have hstep := openGraph_adj_height_bounds hvu i
  exact ⟨i,by omega⟩

/-- Real-probability form of the named critical boundary one-arm input at k=0. -/
lemma critical_halfSpace_arm_zero_real {d : ℕ} (i : Fin d) {A : ℝ} (hA : 0 ≤ A)
    (criticalArm : HalfSpaceCriticalArmInput i A) (n : ℕ) (hn : 1 ≤ n) :
    (percolation d (criticalPoint d)).real (halfSpaceArmEvent i 0 n) ≤ A/(n:ℝ)^3 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (criticalArm n hn)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ A/(n:ℝ)^3)] at h
  have hb : halfSpaceArmBase i 0 = (0 : Vertex d) := by
    ext j
    by_cases hj : j = i <;> simp [halfSpaceArmBase,hj]
  simpa only [halfSpaceArmProbability,halfSpaceArmEvent,halfSpaceArmDomain,halfSpaceArmTarget,hb,
    Measure.real] using h

/-- A path from a positive-oriented outer face towards the heart lies below
the face. The existing lower-half-space normalization handles the sign exactly. -/
theorem critical_lowerHalfSpace_heart_bound {d : ℕ} (i : Fin d)
    (C heart : Finset (Vertex d)) (b : ℤ) (v : Vertex d) (hv : v i = b)
    (n : ℕ) (hn : 1 ≤ n) (hC : ∀ z ∈ C, z i ≤ b)
    (hheart : ∀ z ∈ heart, z i ≤ b-(n:ℤ)) {A : ℝ} (hA : 0 ≤ A)
    (criticalArm : HalfSpaceCriticalArmInput i A) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) ≤ A/(n:ℝ)^3 := by
  have hs : connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d)) ⊆
      connectionToSetEvent {z | z i ≤ b} v {z | z i ≤ b-(n:ℤ)} :=
    connectionToSetEvent_mono (fun z hz => hC z hz) (fun z hz => hheart z hz) v
  have he := lowerHalfSpace_probability_normalize (criticalPoint d) i b 0 n v (by simpa using hv)
  have her : (percolation d (criticalPoint d)).real
      (connectionToSetEvent {z | z i ≤ b} v {z | z i ≤ b-(n:ℤ)}) =
      (percolation d (criticalPoint d)).real (halfSpaceArmEvent i 0 n) := by
    exact congrArg ENNReal.toReal he
  calc
    _ ≤ _ := measureReal_mono hs
    _ = _ := her
    _ ≤ _ := critical_halfSpace_arm_zero_real i hA criticalArm n hn

/-- The negative face uses the upward half-space law; no symmetry of a
truncated finite box is substituted for actual law invariance. -/
theorem critical_upperHalfSpace_heart_bound {d : ℕ} (i : Fin d)
    (C heart : Finset (Vertex d)) (b : ℤ) (v : Vertex d) (hv : v i = b)
    (n : ℕ) (hn : 1 ≤ n) (hC : ∀ z ∈ C, b ≤ z i)
    (hheart : ∀ z ∈ heart, b+(n:ℤ) ≤ z i) {A : ℝ} (hA : 0 ≤ A)
    (criticalArm : HalfSpaceCriticalArmInput i A) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d))) ≤ A/(n:ℝ)^3 := by
  have hs : connectionToSetEvent (C : Set (Vertex d)) v (heart : Set (Vertex d)) ⊆
      connectionToSetEvent {z | b ≤ z i} v {z | b+(n:ℤ) ≤ z i} :=
    connectionToSetEvent_mono (fun z hz => hC z hz) (fun z hz => hheart z hz) v
  have he := upperHalfSpace_probability_normalize (criticalPoint d) i b 0 n v (by simpa using hv)
  have her : (percolation d (criticalPoint d)).real
      (connectionToSetEvent {z | b ≤ z i} v {z | b+(n:ℤ) ≤ z i}) =
      (percolation d (criticalPoint d)).real (halfSpaceArmEvent i 0 n) := by
    exact congrArg ENNReal.toReal he
  calc
    _ ≤ _ := measureReal_mono hs
    _ = _ := her
    _ ≤ _ := critical_halfSpace_arm_zero_real i hA criticalArm n hn

/-- The exact cut-to-heart radius gap gives the inner factor in the actual
heart-membership BK sum, uniformly over EVERY entry vertex and either sign. -/
theorem centered_inner_heart_probability_le {d R H : ℕ}
    (Q heart : Finset (Vertex d)) (hheart : heart ⊆ centeredBox d H) (hHR : H < R)
    {A : ℝ} (hA : 0 ≤ A) (criticalArm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (v : Vertex d) (hv : v ∈ innerEntryBoundary Q (centeredBox d R)) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d R : Set (Vertex d)) v (heart : Set (Vertex d))) ≤
      A/((R-H:ℕ):ℝ)^3 := by
  have hgap : 1 ≤ R-H := by omega
  obtain ⟨i,hi | hi⟩ := centeredBox_boundary_coordinate
    (innerEntryBoundary_subset_boundarySites Q (centeredBox d R) hv)
  · apply critical_lowerHalfSpace_heart_bound i (centeredBox d R) heart (R:ℤ) v hi
      (R-H) hgap (fun z hz => (mem_centeredBox.mp hz i).2)
      (fun z hz => by have h := (mem_centeredBox.mp (hheart hz) i).2; omega) hA (criticalArm i)
  · apply critical_upperHalfSpace_heart_bound i (centeredBox d R) heart (-(R:ℤ)) v hi
      (R-H) hgap (fun z hz => (mem_centeredBox.mp hz i).1)
      (fun z hz => by have h := (mem_centeredBox.mp (hheart hz) i).1; omega) hA (criticalArm i)

/-- Actual critical heart-membership upper bound with its inner factor now
DERIVED from the named critical half-space arm input. Only the outer box
connection estimate and subsequent boundary-cardinality geometry remain. -/
theorem heartClusterUnion_probability_le_critical_inner_arm {d R H : ℕ}
    (Q heart : Finset (Vertex d)) (hCQ : centeredBox d R ⊆ Q)
    (hheart : heart ⊆ centeredBox d H) (hHR : H < R) (x : Vertex d)
    (hx : x ∉ centeredBox d R) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (criticalArm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B)
    (hprefix : ∀ v ∈ innerEntryBoundary Q (centeredBox d R),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {v}) ≤ A) :
    (percolation d (criticalPoint d)).real {ω | x ∈ heartClusterUnion ω Q heart} ≤
      (A*(B/((R-H:ℕ):ℝ)^3))*((innerEntryBoundary Q (centeredBox d R)).card:ℝ) := by
  have hHC : heart ⊆ centeredBox d R := by
    intro z hz
    apply mem_centeredBox.mpr
    intro i
    have h := mem_centeredBox.mp (hheart hz) i
    constructor <;> omega
  exact heartClusterUnion_probability_le_entry_card (criticalPoint d) Q (centeredBox d R) heart
    hCQ hHC x hx hA hprefix (centered_inner_heart_probability_le Q heart hheart hHR hB criticalArm)

end NearCritical
