module
public import NearCritical.NestRegularBoundary
public import NearCritical.Harris
public import NearCritical.CountableBK

/-! Section 8, eq.biejeobsr and the probability step in Lemma nisnmfs.
All events use the actual finite-heart cluster union and percolation law.
BK and Harris are derived inputs from the library, never covariance premises. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def heartEvent {d : ℕ} (Q H : Finset (Vertex d)) (x : Vertex d) : Set (Configuration d) :=
  connectionToSetEvent (Q : Set (Vertex d)) x (H : Set (Vertex d))

def heartPairEvent {d : ℕ} (Q H : Finset (Vertex d)) (x y : Vertex d) : Set (Configuration d) :=
  heartEvent Q H x ∩ heartEvent Q H y

def heartTripleEvent {d : ℕ} (Q H : Finset (Vertex d)) (x y z : Vertex d) : Set (Configuration d) :=
  heartPairEvent Q H x y ∩ heartEvent Q H z

/-- Literal A(y,z) in source eq.biejeobsr. -/
def heartBranchEvent {d : ℕ} (Q H : Finset (Vertex d)) (x y z : Vertex d) : Set (Configuration d) :=
  heartTripleEvent Q H x y z \ {ω | DisjointOccurrence (heartPairEvent Q H x y) (heartEvent Q H z) ω}

lemma measurableSet_heartEvent {d : ℕ} (Q H : Finset (Vertex d)) (x : Vertex d) :
    MeasurableSet (heartEvent Q H x) := measurableSet_connectionToSetEvent _ _ _

lemma heartEvent_increasing {d : ℕ} (Q H : Finset (Vertex d)) (x : Vertex d) :
    BK.Increasing (heartEvent Q H x) := connectionToSetEvent_increasing _ _ _

lemma heartEvent_iff_union_member {d : ℕ} (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (x : Vertex d) (ω : Configuration d) :
    ω ∈ heartEvent Q H x ↔ x ∈ heartClusterUnion ω Q H := by
  constructor
  · rintro ⟨hxQ,y,hyH,_hyQ,hxy⟩
    exact Finset.mem_biUnion.mpr ⟨y,hyH,(mem_finiteBoxCluster ω Q y x).mpr ⟨hxQ,hxy.symm⟩⟩
  · intro hx
    obtain ⟨y,hy,hxy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxQ,hyx⟩ := (mem_finiteBoxCluster ω Q y x).mp hxy
    exact ⟨hxQ,y,hy,hH hy,hyx.symm⟩

private lemma reconstruct_mono {d : ℕ} (Q : Finset (Vertex d))
    {η θ : internalBondSet Q → Bool} (h : BK.ConfigLE η θ) :
    BK.ConfigLE (reconstructInterior Q η) (reconstructInterior Q θ) := by
  intro e he
  by_cases heQ : e ∈ internalBondSet Q
  · have hh := h ⟨e,heQ⟩ (by simpa [reconstructInterior,extendConfiguration,heQ] using he)
    simpa [reconstructInterior,extendConfiguration,heQ] using hh
  · simp [reconstructInterior,extendConfiguration,heQ] at he

private lemma heartEvent_cylinder {d : ℕ} (Q H : Finset (Vertex d)) (x : Vertex d) :
    (internalBondSet Q).restrict ⁻¹' {η | reconstructInterior Q η ∈ heartEvent Q H x} =
      heartEvent Q H x := by
  ext ω
  exact (connectionToSetEvent_iff_of_internalBondSet_agree Q (Q : Set (Vertex d))
    (Subset.rfl) ω _ (reconstructInterior_restrict_agree Q ω) x (H : Set (Vertex d))).symm

/-- Actual heart-event Harris inequality, via exact internal-coordinate law. -/
lemma heartEvent_harris {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d)) (x z : Vertex d) :
    (percolation d p).real (heartEvent Q H x) * (percolation d p).real (heartEvent Q H z) ≤
      (percolation d p).real (heartPairEvent Q H x z) := by
  have h := percolation_cylinder_harris d p (internalBondSet Q)
    {η | reconstructInterior Q η ∈ heartEvent Q H x}
    {η | reconstructInterior Q η ∈ heartEvent Q H z}
    (by intro η θ h hω; exact heartEvent_increasing Q H x (reconstruct_mono Q h) hω)
    (by intro η θ h hω; exact heartEvent_increasing Q H z (reconstruct_mono Q h) hω)
  rw [heartEvent_cylinder,heartEvent_cylinder] at h
  exact h

lemma heartPairEvent_increasing {d : ℕ} (Q H : Finset (Vertex d)) (x y : Vertex d) :
    BK.Increasing (heartPairEvent Q H x y) := by
  intro ω η h hω
  exact ⟨heartEvent_increasing Q H x h hω.1,heartEvent_increasing Q H y h hω.2⟩

lemma measurableSet_heartBranchEvent {d : ℕ} (Q H : Finset (Vertex d)) (x y z : Vertex d) :
    MeasurableSet (heartBranchEvent Q H x y z) := by
  exact (((measurableSet_heartEvent Q H x).inter (measurableSet_heartEvent Q H y)).inter
    (measurableSet_heartEvent Q H z)).diff
      (measurableSet_disjointOccurrence (heartPairEvent_increasing Q H x y) (heartEvent_increasing Q H z))

/-- Source eq.pnoowp2, with its actual branch event rather than a diagram premise. -/
theorem heartTriple_probability_le {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z : Vertex d) :
    (percolation d p).real (heartTripleEvent Q H x y z) ≤
      (percolation d p).real (heartPairEvent Q H x y) * (percolation d p).real (heartEvent Q H z) +
        (percolation d p).real (heartBranchEvent Q H x y z) := by
  let D : Set (Configuration d) := {ω | DisjointOccurrence (heartPairEvent Q H x y) (heartEvent Q H z) ω}
  have hs : heartTripleEvent Q H x y z ⊆ D ∪ heartBranchEvent Q H x y z := by
    intro ω hω
    by_cases hd : ω ∈ D
    · exact Or.inl hd
    · exact Or.inr ⟨hω,hd⟩
  have hb := percolation_bk d p (heartPairEvent Q H x y) (heartEvent Q H z)
    (heartPairEvent_increasing Q H x y) (heartEvent_increasing Q H z)
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans
    (by dsimp [D]; linarith [hb]))

/-- Source eq.eothopb bound, with both BK and positive association discharged. -/
theorem heart_conditional_covariance_le {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z : Vertex d) :
    (percolation d p).real (heartEvent Q H x) * (percolation d p).real (heartTripleEvent Q H x y z) -
      (percolation d p).real (heartPairEvent Q H x y) * (percolation d p).real (heartPairEvent Q H x z) ≤
    (percolation d p).real (heartEvent Q H x) * (percolation d p).real (heartBranchEvent Q H x y z) := by
  have h1 := mul_le_mul_of_nonneg_left (heartTriple_probability_le p Q H x y z)
    (show 0 ≤ (percolation d p).real (heartEvent Q H x) from measureReal_nonneg)
  have h2 := mul_le_mul_of_nonneg_left (heartEvent_harris p Q H x z)
    (show 0 ≤ (percolation d p).real (heartPairEvent Q H x y) from measureReal_nonneg)
  nlinarith

/-- The full nonnegative weighted double-sum bound in source eq.vekboqqeo.
There is no finiteness or positivity assumption on the conditioning probability. -/
theorem heart_weighted_covariance_sum_le {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ) (hf : ∀ y ∈ Q, 0 ≤ f y) :
    (∑ y ∈ Q, ∑ z ∈ Q, f y*f z *
      ((percolation d p).real (heartEvent Q H x) * (percolation d p).real (heartTripleEvent Q H x y z) -
        (percolation d p).real (heartPairEvent Q H x y) * (percolation d p).real (heartPairEvent Q H x z))) ≤
    (percolation d p).real (heartEvent Q H x) *
      (∑ y ∈ Q, ∑ z ∈ Q, f y*f z * (percolation d p).real (heartBranchEvent Q H x y z)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have h := mul_le_mul_of_nonneg_left (heart_conditional_covariance_le p Q H x y z)
    (mul_nonneg (hf y hy) (hf z hz))
  exact h.trans_eq (by ring)

end NearCritical.Section8
