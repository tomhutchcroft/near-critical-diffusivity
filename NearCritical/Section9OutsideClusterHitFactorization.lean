module
public import NearCritical.Section9ClosedFiberLaw
public import NearCritical.Section9PivotalCount

/-! Actual outside-component hit events factor from the revealed cluster fiber. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- A hit in a domain disjoint from C factors from the actual left-cluster
fiber C. This follows from the proved fixed-mask law, not an independence
premise, and includes zero-probability fibers and arbitrary roots. -/
theorem section9_outside_cluster_hit_factorization {d : ℕ} (p : unitInterval)
    (L Q₁ F₁ C D Q₃ F₃ B : Finset (Vertex d)) (root v : Vertex d)
    (hDC : Disjoint D C) :
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
    let H : Set (Configuration d) := {ω | (sprinklingUnexploredCluster ω D Q₃ F₃ v ∩ B).Nonempty}
    (percolation d p).real (E ∩ H) = (percolation d p).real E * (percolation d p).real H := by
  intro E H
  let S := sprinklingClusterFiberMask L Q₁ F₁ C
  let G := sprinklingAvailableBonds D Q₃ F₃
  let close := fun ω : Configuration d => resampleBonds S ω (fun _ => false)
  let f : (G → Bool) → ℝ := fun ξ =>
    if extendConfiguration G (fun _ => false) ξ ∈ H then 1 else 0
  have hH : MeasurableSet H := measurableSet_sprinklingUnexploredCluster_hits D Q₃ F₃ B v
  have hE : MeasurableSet E := by
    have hc := section9_two_cluster_fiber_cylinder L ∅ Q₁ F₁ ∅ ∅ C ∅ (root,root)
    have hempty (ω : Configuration d) : sprinklingUnexploredCluster ω ∅ ∅ ∅ root = ∅ := by
      simp [sprinklingUnexploredCluster]
    have heq : E = section9TwoClusterFiberEvent L ∅ Q₁ F₁ ∅ ∅ C ∅ (root,root) := by
      ext ω
      simp [E,section9TwoClusterFiberEvent,hempty]
    rw [heq,hc]
    exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict _)
  have hrepr (ω : Configuration d) : f (G.restrict ω) = H.indicator (fun _ => (1 : ℝ)) ω := by
    let θ := extendConfiguration G (fun _ => false) (G.restrict ω)
    have heq := sprinklingUnexploredCluster_eq_of_available_agree D Q₃ F₃ θ ω
      (by
        intro b hb
        have hbG : b ∈ G := hb
        simp [θ,extendConfiguration,hbG]) v
    have hm : θ ∈ H ↔ ω ∈ H := by
      simp only [H,Set.mem_setOf_eq,heq]
    change (if θ ∈ H then (1 : ℝ) else 0) = H.indicator (fun _ => (1 : ℝ)) ω
    simp only [Set.indicator_apply,hm]
  have hclose (ω : Configuration d) :
      sprinklingUnexploredCluster (close ω) D Q₃ F₃ v =
        sprinklingUnexploredCluster ω D Q₃ F₃ v := by
    apply sprinklingUnexploredCluster_eq_of_available_agree
    intro b hb
    have hbD := (mem_internalBondSet D b).mp (Finset.mem_sdiff.mp hb).1
    have hbNot : b ∉ S := by
      intro hbS
      rcases (Finset.mem_filter.mp hbS).2 with hbase | htip
      · exact Finset.disjoint_left.mp hDC hbD.1 hbase
      · exact Finset.disjoint_left.mp hDC hbD.2 htip
    simp only [close,resampleBonds,extendConfiguration,dif_neg hbNot]
  have hind (ω : Configuration d) :
      H.indicator (fun _ => (1 : ℝ)) (close ω) = H.indicator (fun _ => (1 : ℝ)) ω := by
    have hm : close ω ∈ H ↔ ω ∈ H := by simp only [H,Set.mem_setOf_eq,hclose]
    simp only [Set.indicator_apply,hm]
  have hprod (ω : Configuration d) :
      E.indicator (fun _ => (1 : ℝ)) ω * H.indicator (fun _ => (1 : ℝ)) ω =
        (E ∩ H).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases he : ω ∈ E <;> by_cases hh : ω ∈ H <;>
      simp only [Set.indicator_apply,Set.mem_inter_iff,he,hh,ite_true,ite_false,
        and_self,and_false,false_and,mul_one,mul_zero,zero_mul]
  have hf := section9_closed_single_cluster_observable_factorization p L Q₁ F₁ C root G f
  change (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * f (G.restrict (close ω)) ∂percolation d p) =
    (percolation d p).real E * (∫ ω, f (G.restrict (close ω)) ∂percolation d p) at hf
  simp_rw [hrepr,hind,hprod] at hf
  have hone : (fun _ : Configuration d => (1 : ℝ)) = (1 : Configuration d → ℝ) := by
    funext ω
    simp only [Pi.one_apply]
  have hiEH : (∫ ω, (E ∩ H).indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) =
      (percolation d p).real (E ∩ H) := by
    rw [hone]
    exact integral_indicator_one (μ := percolation d p) (hE.inter hH)
  have hiH : (∫ ω, H.indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) =
      (percolation d p).real H := by
    rw [hone]
    exact integral_indicator_one (μ := percolation d p) hH
  rw [hiEH,hiH] at hf
  exact hf

end NearCritical
