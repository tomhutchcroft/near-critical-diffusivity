module

public import NearCritical.ClusterCountConcentration
public import NearCritical.CriticalTriangle

/-! Source eq.var.N: size cap and actual finite two-point sums control the
computed count error. Derivation of the spatial input from (A) remains open. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

lemma rootedPropertyPairError_nonneg {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (r s : Vertex d) :
    0 ≤ rootedPropertyPairError p U P r s := by
  apply add_nonneg (measureReal_nonneg)
  apply integral_nonneg
  intro ω
  apply mul_nonneg
  · unfold rootedPropertyIndicator
    split_ifs <;> norm_num
  · exact Finset.sum_nonneg (fun u _ => measureReal_nonneg)

/-- Literal pointwise source size-cap/spatial-sum deduction. Original cluster
weights remain actual; no expectation or variance bound is assumed. -/
lemma rootedProperty_mass_spatial_bound {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {V L : ℝ} (hL : 0 ≤ L)
    (hspatial : ∀ u ∈ U, (∑ s ∈ Z, twoPoint d p s u) ≤ L)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V)
    (r : Vertex d) (hr : r ∈ Z) (ω : Configuration d) :
    (∑ s ∈ Z, rootedPropertyIndicator U P r ω *
      (∑ u ∈ finiteBoxCluster ω U r, twoPoint d p s u)) ≤
      V*L*rootedPropertyIndicator U P r ω := by
  by_cases hp : rootedClusterProperty U r P ω
  · simp only [rootedPropertyIndicator, if_pos hp, one_mul, mul_one]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _u ∈ finiteBoxCluster ω U r, L := Finset.sum_le_sum
        (fun u hu => hspatial u (finiteBoxCluster_subset ω U r hu))
      _ = ((finiteBoxCluster ω U r).card:ℝ)*L := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcap ω r hr hp) hL
  · simp [rootedPropertyIndicator, hp]

private lemma integrable_property_mass {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r : Vertex d) (hr : r ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (s : Vertex d) :
    Integrable (fun ω => rootedPropertyIndicator U P r ω *
      (∑ u ∈ finiteBoxCluster ω U r, twoPoint d p s u)) (percolation d p) := by
  have hi (u : Vertex d) := (integrable_rootedPropertyIndicator p U r hr
    (fun G C => P G C ∧ u ∈ C)).mul_const (twoPoint d p s u)
  apply (integrable_finsetSum U (fun u _ => hi u)).congr
  filter_upwards [] with ω
  calc
    (∑ u ∈ U, rootedPropertyIndicator U (fun G C => P G C ∧ u ∈ C) r ω * twoPoint d p s u) =
        ∑ u ∈ finiteBoxCluster ω U r,
          rootedPropertyIndicator U (fun G C => P G C ∧ u ∈ C) r ω * twoPoint d p s u := by
      symm
      apply Finset.sum_subset (finiteBoxCluster_subset ω U r)
      intro u _hu hn
      simp [rootedPropertyIndicator, rootedClusterProperty, hn]
    _ = ∑ u ∈ finiteBoxCluster ω U r, rootedPropertyIndicator U P r ω * twoPoint d p s u := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [rootedPropertyIndicator, rootedClusterProperty, hu,ite_mul]
      by_cases hP : P (restrictedGraph ω (finiteBoxCluster ω U r : Set (Vertex d)))
          (finiteBoxCluster ω U r) <;> simp only [hP,if_true,if_false,one_mul,zero_mul]
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Average the pointwise size-cap/spatial-sum deduction, with actual derived
integrability for each original random-component mass. -/
theorem rootedProperty_mass_spatial_expectation {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {V L : ℝ} (hL : 0 ≤ L)
    (hspatial : ∀ u ∈ U, (∑ s ∈ Z, twoPoint d p s u) ≤ L)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V) (r : Vertex d) (hr : r ∈ Z) :
    (∑ s ∈ Z, ∫ ω, rootedPropertyIndicator U P r ω *
      (∑ u ∈ finiteBoxCluster ω U r, twoPoint d p s u) ∂percolation d p) ≤
      V*L*(∫ ω, rootedPropertyIndicator U P r ω ∂percolation d p) := by
  rw [← integral_finsetSum Z (fun s _ => integrable_property_mass p U r (hZU hr) P s),
    ← integral_const_mul]
  exact integral_mono (integrable_finsetSum Z
    (fun s _ => integrable_property_mass p U r (hZU hr) P s))
    ((integrable_rootedPropertyIndicator p U r (hZU hr) P).const_mul (V*L))
    (rootedProperty_mass_spatial_bound p U Z P hL hspatial hcap r hr)

/-- Full ordered-pair source error sum. The actual global connection sum uses
symmetry; the random-cluster error uses the volume cap and source spatial sum. -/
theorem rootedPropertyPairError_spatial_sum {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {V L : ℝ} (hL : 0 ≤ L)
    (hspatial : ∀ u ∈ U, (∑ s ∈ Z, twoPoint d p s u) ≤ L)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V) :
    (∑ r ∈ Z, ∑ s ∈ Z, rootedPropertyPairError p U P r s) ≤
      (Z.card:ℝ)*L + V*L*rootedPropertyCountMean p U Z P := by
  have ht : (∑ r ∈ Z, ∑ s ∈ Z, twoPoint d p r s) ≤ (Z.card:ℝ)*L := by
    calc
      _ ≤ ∑ _r ∈ Z, L := by
        apply Finset.sum_le_sum
        intro r hr
        have he : (∑ s ∈ Z, twoPoint d p r s) = ∑ s ∈ Z, twoPoint d p s r := by
          apply Finset.sum_congr rfl
          intro s _hs
          exact twoPoint_symm p r s
        rw [he]
        exact hspatial r (hZU hr)
      _ = _ := by simp [mul_comm]
  have hm : (∑ r ∈ Z, ∑ s ∈ Z, ∫ ω, rootedPropertyIndicator U P r ω *
      (∑ u ∈ finiteBoxCluster ω U r, twoPoint d p s u) ∂percolation d p) ≤
      V*L*rootedPropertyCountMean p U Z P := by
    calc
      _ ≤ ∑ r ∈ Z, V*L*(∫ ω, rootedPropertyIndicator U P r ω ∂percolation d p) :=
        Finset.sum_le_sum (fun r hr => rootedProperty_mass_spatial_expectation p U Z hZU P
          hL hspatial hcap r hr)
      _ = V*L*(∑ r ∈ Z, ∫ ω, rootedPropertyIndicator U P r ω ∂percolation d p) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by
        rw [← integral_finsetSum Z
          (fun r hr => integrable_rootedPropertyIndicator p U r (hZU hr) P)]
        rfl
  have h := add_le_add ht hm
  simpa only [rootedPropertyPairError, twoPoint, Finset.sum_add_distrib] using h

/-- Actual source centered-moment estimate from raw volume/spatial data.
The spatial hypothesis is explicit and still needs instantiation from (A). -/
theorem rootedPropertyCount_centered_spatial_bound {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {V L : ℝ} (hL : 0 ≤ L)
    (hspatial : ∀ u ∈ U, (∑ s ∈ Z, twoPoint d p s u) ≤ L)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V) :
    (∫ ω, (rootedPropertyCount U Z P ω-rootedPropertyCountMean p U Z P)^2
      ∂percolation d p) ≤
      rootedPropertyCountMean p U Z P + (Z.card:ℝ)*L +
        V*L*rootedPropertyCountMean p U Z P := by
  have hf : (∑ r ∈ Z, ∑ s ∈ Z, if r = s then 0 else rootedPropertyPairError p U P r s) ≤
      ∑ r ∈ Z, ∑ s ∈ Z, rootedPropertyPairError p U P r s := by
    apply Finset.sum_le_sum
    intro r _hr
    apply Finset.sum_le_sum
    intro s _hs
    split_ifs
    · exact rootedPropertyPairError_nonneg p U P r s
    · exact le_rfl
  have he := hf.trans (rootedPropertyPairError_spatial_sum p U Z hZU P hL hspatial hcap)
  have hbase := rootedPropertyCount_centered_le p U Z hZU P
  unfold rootedPropertyCountError at hbase
  have h := hbase.trans (add_le_add (le_refl (rootedPropertyCountMean p U Z P)) he)
  simpa only [rootedPropertyCountError, add_assoc] using h

end NearCritical
