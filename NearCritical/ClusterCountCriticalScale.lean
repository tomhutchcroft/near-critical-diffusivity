module

public import NearCritical.ClusterCountCriticalVariance

/-! Source eq.var.N scale deduction from actual(A), root cardinality, actual
mean upper bound and raw selected-cluster size window. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

private lemma count_spatial_scale {d : ℕ} (hd : 2 ≤ d) {n m z K Cz Cm Cv : ℝ}
    (hn : 1 ≤ n) (hK : 0 ≤ K) (hCz : 0 ≤ Cz) (hCm : 0 ≤ Cm) (hCv : 0 ≤ Cv)
    (hz : z ≤ Cz*n^d) (hm : m ≤ Cm*n^(d-2)) :
    m+z*(K*n^2)+(Cv*n^4)*(K*n^2)*m ≤
      (1+Cm+Cz*K+Cv*K*Cm)*n^(d+4) := by
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have hcoef : 0 ≤ (Cv*n^4)*(K*n^2) := by positivity
  have hp2 : n^(d+2) = n^d*n^2 := pow_add n d 2
  have hp6 : n^(d+4) = n^4*n^2*n^(d-2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hpm : n^(d-2) ≤ n^(d+4) := pow_le_pow_right₀ hn (by omega)
  have hpz : n^(d+2) ≤ n^(d+4) := pow_le_pow_right₀ hn (by omega)
  have hCzK : 0 ≤ Cz*K := mul_nonneg hCz hK
  calc
    _ ≤ Cm*n^(d-2)+(Cz*n^d)*(K*n^2)+(Cv*n^4)*(K*n^2)*(Cm*n^(d-2)) := by
      exact add_le_add (add_le_add hm (mul_le_mul_of_nonneg_right hz (by positivity)))
        (mul_le_mul_of_nonneg_left hm hcoef)
    _ = Cm*n^(d-2)+(Cz*K)*n^(d+2)+(Cv*K*Cm)*n^(d+4) := by
      rw [hp2, hp6]
      ring
    _ ≤ Cm*n^(d+4)+(Cz*K)*n^(d+4)+(Cv*K*Cm)*n^(d+4) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hpm hCm)
        (mul_le_mul_of_nonneg_left hpz hCzK)) le_rfl
    _ = (Cm+Cz*K+Cv*K*Cm)*n^(d+4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hn0 _)

/-- Literal source n^(d+4) centered-moment rate with ONE constant before all
radii, root sets and cluster properties. Actual(A) supplies the spatial input;
mean and size-window data are explicit, not variance/failure hypotheses. -/
theorem critical_rootedPropertyCount_variance_scale {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) {Cz Cm Cv : ℝ}
    (hCz : 0 ≤ Cz) (hCm : 0 ≤ Cm) (hCv : 0 ≤ Cv) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      ∀ (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop),
      (Z.card:ℝ) ≤ Cz*(N+1:ℝ)^d →
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P ≤ Cm*(N+1:ℝ)^(d-2) →
      (∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r P ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4) →
      (∫ ω, (rootedPropertyCount (centeredBox d N) Z P ω -
        rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)^2
        ∂percolation d (criticalPoint d)) ≤ C*(N+1:ℝ)^(d+4) := by
  obtain ⟨K, hK, hvar⟩ := critical_rootedPropertyCount_centered_bound hd hA
  refine ⟨1+Cm+Cz*K+Cv*K*Cm, by positivity, ?_⟩
  intro N Z hZ P hcard hmean hcap
  have hn : (1:ℝ) ≤ (N+1:ℝ) := by exact_mod_cast (Nat.le_add_left 1 N)
  have h := hvar N Z hZ P (Cv*(N+1:ℝ)^4) hcap
  exact h.trans (count_spatial_scale hd hn hK.le hCz hCm hCv hcard hmean)

/-- Actual centered-box cardinality discharges the generic root-cardinality
input. Only the computed mean upper bound and raw volume window remain. -/
theorem critical_rootedPropertyCount_variance_scale_of_box {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) {Cm Cv : ℝ} (hCm : 0 ≤ Cm) (hCv : 0 ≤ Cv) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      ∀ (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop),
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P ≤ Cm*(N+1:ℝ)^(d-2) →
      (∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r P ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ Cv*(N+1:ℝ)^4) →
      (∫ ω, (rootedPropertyCount (centeredBox d N) Z P ω -
        rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)^2
        ∂percolation d (criticalPoint d)) ≤ C*(N+1:ℝ)^(d+4) := by
  obtain ⟨C, hC, hb⟩ := critical_rootedPropertyCount_variance_scale hd hA
    (Cz := (2:ℝ)^d) (by positivity) hCm hCv
  refine ⟨C, hC, ?_⟩
  intro N Z hZ P hmean hcap
  have hcard : (Z.card:ℝ) ≤ (2:ℝ)^d*(N+1:ℝ)^d := by
    have hz : (Z.card:ℝ) ≤ ((centeredBox d N).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hZ
    have hc : ((centeredBox d N).card:ℝ) = (2*(N:ℝ)+1)^d := by
      rw [centeredBox_eq_latticeSupCube]
      exact_mod_cast card_latticeSupCube d N
    calc
      _ ≤ (2*(N:ℝ)+1)^d := hz.trans_eq hc
      _ ≤ (2*(N+1:ℝ))^d := pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = _ := mul_pow _ _ _
  exact hb N Z hZ P hcard hmean hcap

end NearCritical
