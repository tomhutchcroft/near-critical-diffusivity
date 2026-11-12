module

public import NearCritical.CriticalBoxMass
public import NearCritical.CriticalTriangle
public import NearCritical.HeartConnectionCount

/-! Actual restricted component volume for prop.num_spanning_new Step1.
The mean and large-volume tail are deduced from assumption (A); no moment
or volume-tail estimate is a premise. Source radius rounding, spanning lower
probability and small-volume tightness remain separate obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

lemma heartConnectionCount_full_target {d : ℕ} (Q : Finset (Vertex d))
    (x : Vertex d) (ω : Configuration d) :
    heartConnectionCount Q Q x ω = ((finiteBoxCluster ω Q x).card : ℝ) := by
  have he : Q.filter (fun y => y ∈ finiteBoxCluster ω Q x) = finiteBoxCluster ω Q x := by
    ext y
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hy => finiteBoxCluster_subset ω Q x hy)
  simp only [heartConnectionCount, he]

lemma integrable_finiteBoxCluster_card {d : ℕ} (p : unitInterval)
    (Q : Finset (Vertex d)) (x : Vertex d) :
    Integrable (fun ω => ((finiteBoxCluster ω Q x).card : ℝ)) (percolation d p) := by
  simpa only [heartConnectionCount_full_target] using
    integrable_heartConnectionCount_observable p Q Q x (fun z => z)

/-- The actual finite mean is bounded by the actual unrestricted two-point
mass, with no susceptibility or expected-volume input. -/
theorem integral_finiteBoxCluster_card_le_twoPoint {d : ℕ} (p : unitInterval)
    (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) :
    (∫ ω, ((finiteBoxCluster ω Q x).card : ℝ) ∂percolation d p) ≤
      ∑ y ∈ Q, twoPoint d p y x := by
  calc
    _ = ∫ ω, heartConnectionCount Q Q x ω ∂percolation d p := by
      simp_rw [heartConnectionCount_full_target]
    _ = ∑ y ∈ Q, (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) :=
      integral_heartConnectionCount p Q Q x hx
    _ ≤ ∑ y ∈ Q, twoPoint d p y x := by
      apply Finset.sum_le_sum
      intro y _hy
      rw [twoPoint_symm p y x]
      refine measureReal_mono ?_ (by finiteness)
      rintro ω ⟨_hx,z,hz,_hzQ,hpath⟩
      have hzy : z = y := hz
      subst z
      have hle : restrictedGraph ω (Q : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
      exact hpath.mono hle

/-- ONE constant before all radii, finite subdomains, and roots bounds the
actual critical restricted component mean by the square of the box scale. -/
theorem critical_finiteBoxCluster_mean_le {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (Q : Finset (Vertex d)), Q ⊆ centeredBox d N →
      ∀ x ∈ Q,
        (∫ ω, ((finiteBoxCluster ω Q x).card : ℝ) ∂percolation d (criticalPoint d)) ≤
          K*(N+1:ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := critical_twoPoint_mass_in_centered_box hd hA
  refine ⟨K,hK,?_⟩
  intro N Q hQ x hx
  exact (integral_finiteBoxCluster_card_le_twoPoint (criticalPoint d) Q x hx).trans
    (hbound N Q hQ x (hQ hx))

/-- Source Step1 large-volume estimate at the actual n^4 scale. -/
theorem critical_finiteBoxCluster_volume_tail {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (Q : Finset (Vertex d)), Q ⊆ centeredBox d N →
      ∀ x ∈ Q, ∀ C : ℝ, 0 < C →
        (percolation d (criticalPoint d)).real
          {ω | C*(N+1:ℝ)^4 ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ≤
            K/(C*(N+1:ℝ)^2) := by
  obtain ⟨K,hK,hmean⟩ := critical_finiteBoxCluster_mean_le hd hA
  refine ⟨K,hK,?_⟩
  intro N Q hQ x hx C hC
  have hn : 0 < (N+1:ℝ) := by positivity
  have ht : 0 < C*(N+1:ℝ)^4 := by positivity
  have hnon : 0 ≤ᵐ[percolation d (criticalPoint d)]
      (fun ω => ((finiteBoxCluster ω Q x).card : ℝ)) := by
    filter_upwards [] with ω
    positivity
  have hm := mul_meas_ge_le_integral_of_nonneg hnon
    (integrable_finiteBoxCluster_card (criticalPoint d) Q x) (C*(N+1:ℝ)^4)
  have hb := hm.trans (hmean N Q hQ x hx)
  have hc : (K/(C*(N+1:ℝ)^2))*(C*(N+1:ℝ)^4) = K*(N+1:ℝ)^2 := by
    field_simp [ne_of_gt hC, ne_of_gt hn]
    <;> ring
  have hb' : (percolation d (criticalPoint d)).real
      {ω | C*(N+1:ℝ)^4 ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ≤
        (K*(N+1:ℝ)^2)/(C*(N+1:ℝ)^4) := by
    apply (le_div_iff₀ ht).mpr
    exact (mul_comm _ _).trans_le hb
  calc
    _ ≤ (K*(N+1:ℝ)^2)/(C*(N+1:ℝ)^4) := hb'
    _ = K/(C*(N+1:ℝ)^2) := (div_eq_iff ht.ne').mpr hc.symm

/-- Joint large-volume/spanning ratio: a raw actual spanning-probability
lower bound c/n^2 yields a uniform K/(C*c) upper-volume conditional ratio.
The event is arbitrary; no unproved spanning geometry or positivity is hidden. -/
theorem critical_finiteBoxCluster_volume_joint_ratio {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (Q : Finset (Vertex d)), Q ⊆ centeredBox d N →
      ∀ x ∈ Q, ∀ C c : ℝ, 0 < C → 0 < c →
      ∀ S : Set (Configuration d),
        c/(N+1:ℝ)^2 ≤ (percolation d (criticalPoint d)).real S →
        (percolation d (criticalPoint d)).real
          ({ω | C*(N+1:ℝ)^4 ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ∩ S) /
            (percolation d (criticalPoint d)).real S ≤ K/(C*c) := by
  obtain ⟨K,hK,htail⟩ := critical_finiteBoxCluster_volume_tail hd hA
  refine ⟨K,hK,?_⟩
  intro N Q hQ x hx C c hC hc S hS
  have hn : 0 < (N+1:ℝ) := by positivity
  have hsmall : 0 < c/(N+1:ℝ)^2 := by positivity
  have hbound := (measureReal_mono (Set.inter_subset_left :
    ({ω : Configuration d | C*(N+1:ℝ)^4 ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ∩ S) ⊆
      {ω | C*(N+1:ℝ)^4 ≤ ((finiteBoxCluster ω Q x).card : ℝ)})).trans
        (htail N Q hQ x hx C hC)
  calc
    _ ≤ (K/(C*(N+1:ℝ)^2))/(percolation d (criticalPoint d)).real S :=
      div_le_div_of_nonneg_right hbound measureReal_nonneg
    _ ≤ (K/(C*(N+1:ℝ)^2))/(c/(N+1:ℝ)^2) :=
      div_le_div_of_nonneg_left (by positivity) hsmall hS
    _ = K/(C*c) := by
      field_simp [ne_of_gt hC, ne_of_gt hc, ne_of_gt hn]
      <;> ring

end NearCritical
