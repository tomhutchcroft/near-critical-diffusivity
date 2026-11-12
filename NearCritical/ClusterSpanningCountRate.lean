module

public import NearCritical.ClusterSpanningCountMean
public import NearCritical.ClusterCriticalDistinctCount

/-! Source prop.num_spanning_new assembled lower-count rate. Mean, variance,
volume cap and count-tail conclusions are not hypotheses. Raw actual spanning,
property, small-volume and root-density inputs still require instantiation. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

private lemma count_scale_cancel {d : ℕ} (hd : 2 ≤ d) {n : ℝ} (hn : 0 < n)
    (A B : ℝ) : (A/n^2)*(B*n^d) = (A*B)*n^(d-2) := by
  have hp : n^d = n^(d-2)*n^2 := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hp]
  field_simp [ne_of_gt hn]
  <;> ring

/-- Uniform actual distinct-window-component failure rate. The threshold is
positive times n^(d-6), and failure is O(n^(8-d)). Only raw Step1 data remain. -/
theorem critical_spanningWindow_distinct_failure_rate {d : ℕ} (hd : 9 ≤ d)
    (hA : TwoPointAsymptotics d) (δ c Cs cz Cz : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hCs : 0 ≤ Cs) (hcz : 0 < cz) (hCz : 0 ≤ Cz) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      cz*(N+1:ℝ)^d ≤ (Z.card:ℝ) → (Z.card:ℝ) ≤ Cz*(N+1:ℝ)^d →
      ∀ (φ : Type*) (faces : φ → Finset (Vertex d))
        (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a : ℝ),
      (∀ x ∈ Z, c/(N+1:ℝ)^2 ≤ (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) faces x)) →
      (∀ x ∈ Z, (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) faces x) ≤ Cs/(N+1:ℝ)^2) →
      (∀ x ∈ Z, δ*(percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) faces x) ≤
        (percolation d (criticalPoint d)).real
          ({ω | rootedClusterProperty (centeredBox d N) x P ω} ∩
            finiteRootSpanningEvent (centeredBox d N) faces x)) →
      (∀ x ∈ Z, (percolation d (criticalPoint d)).real
        ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card:ℝ) ≤ a} ∩
          finiteRootSpanningEvent (centeredBox d N) faces x) ≤
        (δ/4)*(percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) faces x)) →
      (percolation d (criticalPoint d)).real {ω |
        ((selectedPropertyComponents (centeredBox d N) Z
          (spanningWindowProperty faces P a (C*(N+1:ℝ)^4)) ω).card:ℝ) ≤
            ((δ*c*cz/4)/C)*(N+1:ℝ)^(d-6)} ≤ D/(N+1:ℝ)^(d-8) := by
  obtain ⟨C,hC,hmean⟩ := critical_spanningWindow_count_mean (by omega : 2 ≤ d) hA δ c Cs hδ hc
  let cm : ℝ := (δ*c/2)*cz
  let Cm : ℝ := Cs*Cz
  have hcm : 0 < cm := by dsimp [cm]; positivity
  have hCm : 0 ≤ Cm := mul_nonneg hCs hCz
  obtain ⟨D,hD,hrate⟩ := critical_distinctPropertyCount_failure_rate hd hA hCm hC hcm
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨C,D,hC,hD,?_⟩
  intro N Z hZ hcardlo hcardhi φ faces P a hspanlo hspanhi hproperty hlow
  let W := spanningWindowProperty faces P a (C*(N+1:ℝ)^4)
  have hm := hmean N (centeredBox d N) Z (fun _ h => h) hZ φ faces P a
    hspanlo hspanhi hproperty hlow
  have hn : 0 < (N+1:ℝ) := by positivity
  have hlo : cm*(N+1:ℝ)^(d-2) ≤
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z W := by
    calc
      _ = ((δ*c/2)/(N+1:ℝ)^2)*(cz*(N+1:ℝ)^d) :=
        (count_scale_cancel (by omega : 2 ≤ d) hn (δ*c/2) cz).symm
      _ ≤ ((δ*c/2)/(N+1:ℝ)^2)*(Z.card:ℝ) :=
        mul_le_mul_of_nonneg_left hcardlo (by positivity)
      _ ≤ _ := hm.1
  have hhi : rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z W ≤
      Cm*(N+1:ℝ)^(d-2) := by
    calc
      _ ≤ (Cs/(N+1:ℝ)^2)*(Z.card:ℝ) := hm.2
      _ ≤ (Cs/(N+1:ℝ)^2)*(Cz*(N+1:ℝ)^d) :=
        mul_le_mul_of_nonneg_left hcardhi (by positivity)
      _ = _ := count_scale_cancel (by omega : 2 ≤ d) hn Cs Cz
  have hcap : ∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r W ω →
      ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ C*(N+1:ℝ)^4 := by
    intro ω r _hr h
    exact spanningWindow_selected_volume_le (centeredBox d N) faces P a (C*(N+1:ℝ)^4) ω r h
  have hb := hrate N Z hZ W hlo hhi hcap
  have he : ((1/2:ℝ)*cm/C) = (δ*c*cz/4)/C := by dsimp [cm]; ring
  simpa only [he] using hb

end NearCritical
