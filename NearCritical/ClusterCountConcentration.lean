module

public import NearCritical.ClusterCountMoments

/-! Actual centered count moment and concentration in prop.num_spanning_new.
The source moment expression is derived, not supplied as a variance premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

def rootedPropertyCountMean {d : ℕ} (p : unitInterval) (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) : ℝ :=
  ∫ ω, rootedPropertyCount U Z P ω ∂percolation d p

/-- The computed source expression bounding the centered moment, not a supplied
variance estimate: first mean plus all actual off-diagonal pair errors. -/
def rootedPropertyCountError {d : ℕ} (p : unitInterval) (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) : ℝ :=
  rootedPropertyCountMean p U Z P +
    ∑ r ∈ Z, ∑ s ∈ Z, if r = s then 0 else rootedPropertyPairError p U P r s

/-- Exact centered-moment identity for the ACTUAL rooted count. All moments
are integrable by finite internal-coordinate support. -/
theorem rootedPropertyCount_centered_identity {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (rootedPropertyCount U Z P ω - rootedPropertyCountMean p U Z P)^2
      ∂percolation d p) =
    (∫ ω, (rootedPropertyCount U Z P ω)^2 ∂percolation d p) -
      (rootedPropertyCountMean p U Z P)^2 := by
  let N := rootedPropertyCount U Z P
  let m := rootedPropertyCountMean p U Z P
  change (∫ ω, (N ω-m)^2 ∂percolation d p) =
    (∫ ω, (N ω)^2 ∂percolation d p)-m^2
  have hN : Integrable N (percolation d p) :=
    integrable_rootedPropertyCount_observable p U Z hZU P (fun x => x)
  have hN2 : Integrable (fun ω => (N ω)^2) (percolation d p) :=
    integrable_rootedPropertyCount_observable p U Z hZU P (fun x => x^2)
  have hM := hN.const_mul (2*m)
  have hp (ω : Configuration d) : (N ω-m)^2 = (N ω)^2-(2*m)*N ω+m^2 := by ring
  simp_rw [hp]
  have hadd : (∫ ω, (N ω)^2-(2*m)*N ω+m^2 ∂percolation d p) =
      (∫ ω, (N ω)^2-(2*m)*N ω ∂percolation d p) +
        ∫ _ω : Configuration d, m^2 ∂percolation d p := by
    convert! integral_add (hN2.sub hM) (integrable_const (m^2)) using 1
  have hsub : (∫ ω, (N ω)^2-(2*m)*N ω ∂percolation d p) =
      (∫ ω, (N ω)^2 ∂percolation d p) - ∫ ω, (2*m)*N ω ∂percolation d p := by
    convert! integral_sub hN2 hM using 1
  rw [hadd, hsub, integral_const_mul]
  have hc : (∫ _ω : Configuration d, m^2 ∂percolation d p) = m^2 := by simp
  rw [hc]
  change (∫ ω, (N ω)^2 ∂percolation d p)-(2*m)*m+m^2 = _
  ring

/-- The source actual centered-moment bound follows from actual pair
expectations; no variance or covariance estimate is an input. -/
theorem rootedPropertyCount_centered_le {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (rootedPropertyCount U Z P ω - rootedPropertyCountMean p U Z P)^2
      ∂percolation d p) ≤ rootedPropertyCountError p U Z P := by
  rw [rootedPropertyCount_centered_identity p U Z hZU P]
  unfold rootedPropertyCountError rootedPropertyCountMean
  have h := integral_rootedPropertyCount_sq_le p U Z hZU P
  linarith

/-- Actual lower-tail bound with the source's computed moment expression.
No numerical diagram bound or probability conclusion is supplied as a premise. -/
theorem rootedPropertyCount_lower_tail {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {t : ℝ} (ht : 0 < t) :
    (percolation d p).real {ω | rootedPropertyCount U Z P ω ≤
      rootedPropertyCountMean p U Z P - t} ≤ rootedPropertyCountError p U Z P / t^2 := by
  let m := rootedPropertyCountMean p U Z P
  let g := fun ω : Configuration d => (rootedPropertyCount U Z P ω-m)^2
  have hi : Integrable g (percolation d p) :=
    integrable_rootedPropertyCount_observable p U Z hZU P (fun x => (x-m)^2)
  have hn : 0 ≤ᵐ[percolation d p] g := by
    filter_upwards [] with ω
    exact sq_nonneg _
  have hs : {ω : Configuration d | rootedPropertyCount U Z P ω ≤ m-t} ⊆
      {ω | t^2 ≤ g ω} := by
    intro ω hω
    change rootedPropertyCount U Z P ω ≤ m-t at hω
    change t^2 ≤ (rootedPropertyCount U Z P ω-m)^2
    have hp := mul_nonneg
      (show 0 ≤ m-rootedPropertyCount U Z P ω-t by linarith)
      (show 0 ≤ m-rootedPropertyCount U Z P ω+t by linarith)
    nlinarith
  have hm := mul_meas_ge_le_integral_of_nonneg hn hi (t^2)
  have ht2 : 0 < t^2 := by positivity
  have hb : (percolation d p).real {ω | t^2 ≤ g ω} ≤
      rootedPropertyCountError p U Z P / t^2 := by
    apply (le_div_iff₀ ht2).mpr
    calc
      _ = t^2 * (percolation d p).real {ω | t^2 ≤ g ω} := mul_comm _ _
      _ ≤ ∫ ω, g ω ∂percolation d p := hm
      _ ≤ _ := rootedPropertyCount_centered_le p U Z hZU P
  exact (measureReal_mono hs).trans hb

/-- Literal source relative lower-tail concentration, for any lambda<1 and
positive ACTUAL mean. The still-needed numerical error rate stays visible. -/
theorem rootedPropertyCount_relative_lower_tail {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (hm : 0 < rootedPropertyCountMean p U Z P) {«λ» : ℝ} («hλ» : «λ» < 1) :
    (percolation d p).real {ω | rootedPropertyCount U Z P ω ≤
      «λ» * rootedPropertyCountMean p U Z P} ≤
      rootedPropertyCountError p U Z P / ((1-«λ»)*rootedPropertyCountMean p U Z P)^2 := by
  have ht : 0 < (1-«λ»)*rootedPropertyCountMean p U Z P := mul_pos (sub_pos.mpr «hλ») hm
  have h := rootedPropertyCount_lower_tail p U Z hZU P ht
  have he : rootedPropertyCountMean p U Z P-(1-«λ»)*rootedPropertyCountMean p U Z P =
      «λ»*rootedPropertyCountMean p U Z P := by ring
  simpa only [he] using h

end NearCritical
