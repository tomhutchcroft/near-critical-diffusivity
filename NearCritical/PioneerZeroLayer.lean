module

public import NearCritical.HalfSpacePioneerReduction
public import NearCritical.OpenEventHarris

/-! The zero-height pioneer term required in the new half-space argument.
Reuse actual finite-witness Harris only for one additional open bond. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

private lemma connection_finite_witnesses {d : ℕ} (S A : Set (Vertex d)) (x : Vertex d) :
    connectionToSetEvent S x A = ⋃ F : Finset (Bond d), BK.truncation (connectionToSetEvent S x A) F := by
  ext ω
  constructor
  · rintro ⟨hx, y, hy, hyS, ⟨w⟩⟩
    have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1
    let v := w.mapLe hle
    have hv : ∀ z ∈ v.support, z ∈ S := by
      simpa only [v, SimpleGraph.Walk.support_mapLe_eq_support] using restrictedWalk_support w hx
    obtain ⟨F, hopen, _, hforce⟩ := openWalk_certificate v S hv
    apply mem_iUnion.mpr
    refine ⟨F, ?_⟩
    change connectionToSetEvent S x A (Network.certificateConfiguration ω (F : Set (Bond d)))
    obtain ⟨hx', z, hz, hzS, hp⟩ := hforce (Network.certificateConfiguration ω (F : Set (Bond d))) (fun e he => by
      simpa [Network.certificateConfiguration, he] using hopen e he)
    have hzy : z = y := hz
    subst z
    exact ⟨hx', y, hy, hzS, hp⟩
  · intro h
    obtain ⟨F, hF⟩ := mem_iUnion.mp h
    exact BK.truncation_subset (connectionToSetEvent_increasing S x A) F hF

private lemma open_bond_finite_witnesses {d : ℕ} (e : Bond d) :
    {ω : Configuration d | ω e = true} = ⋃ F : Finset (Bond d), BK.truncation {ω | ω e = true} F := by
  ext ω
  constructor
  · intro h
    apply mem_iUnion.mpr
    refine ⟨{e}, ?_⟩
    simpa [BK.truncation, Network.certificateConfiguration] using h
  · intro h
    obtain ⟨F, hF⟩ := mem_iUnion.mp h
    exact BK.truncation_subset (fun _ _ hle hω => hle e hω) F hF

/-- Appending one open positive-coordinate bond, with actual Harris supplying
its survival factor even if the bond belongs to the original path. -/
lemma halfSpace_boundary_extend_probability {d : ℕ} (p : unitInterval) (i : Fin d)
    (u : Vertex d) (hu : u i = 0) :
    ENNReal.ofReal (p : ℝ) *
      percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u}) ≤
      percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {bondTip (u, i)}) := by
  let A := connectionToSetEvent {z : Vertex d | 0 ≤ z i} 0 {u}
  let B := {ω : Configuration d | ω (u, i) = true}
  have hH := percolation_harris_of_finite_witnesses d p
    (connectionToSetEvent_increasing {z | 0 ≤ z i} 0 {u})
    (show BK.Increasing B from fun _ _ hle hω => hle (u, i) hω)
    (connection_finite_witnesses _ _ _) (open_bond_finite_witnesses (u, i))
  rw [percolation_open_bond] at hH
  rw [mul_comm]
  apply hH.trans
  apply measure_mono
  rintro ω ⟨⟨hx, y, hy, hyS, hp⟩, hopen⟩
  have hyu : y = u := hy
  subst y
  have htip : 0 ≤ (bondTip (u, i)) i := by simp [bondTip, hu]
  refine ⟨hx, bondTip (u, i), rfl, htip, hp.trans ?_⟩
  apply SimpleGraph.Adj.reachable
  exact ⟨⟨(u, i), hopen, Or.inl ⟨rfl, rfl⟩⟩, hyS, htip⟩

/-- The missing zero-layer control: p*psi(H_0) <= psi(H_1). No pioneer
finiteness or decay estimate is assumed to prove this actual-law inequality. -/
theorem halfSpace_pioneer_zero_mul_le_one {d : ℕ} (p : unitInterval) (i : Fin d) :
    ENNReal.ofReal (p : ℝ) * halfSpacePioneerMass p i 0 ≤ halfSpacePioneerMass p i 1 := by
  let a : Vertex d := Function.update 0 i 1
  have htip : ∀ u : Vertex d, bondTip (u, i) = u + a := by
    intro u
    ext j
    by_cases hj : j = i
    · subst j; simp [bondTip, a]
    · simp [bondTip, a, Function.update_of_ne hj]
  calc
    _ = ∑' u : Vertex d, if u i = 0 then ENNReal.ofReal (p : ℝ) *
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u}) else 0 := by
      rw [← halfSpace_prefix_sum p i 0, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro u
      split_ifs <;> simp
    _ ≤ ∑' u : Vertex d, if u i = 0 then
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {bondTip (u, i)}) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro u
      split_ifs with hu
      · exact halfSpace_boundary_extend_probability p i u hu
      · rfl
    _ = _ := by
      rw [← halfSpace_prefix_sum p i 1]
      symm
      rw [← (Equiv.addRight a).tsum_eq]
      apply tsum_congr
      intro u
      have hcond : (u + a) i = 1 ↔ u i = 0 := by
        change u i + (Function.update (0 : Vertex d) i (1 : ℤ)) i = 1 ↔ u i = 0
        simp
      change (if (u + a) i = 1 then
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u + a}) else 0) = _
      simp only [hcond, htip]

end NearCritical
