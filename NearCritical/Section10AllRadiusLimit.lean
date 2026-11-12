module

public import NearCritical.Section10CubeTiling
public import NearCritical.Section10LimitLower
public import NearCritical.TriadicDirichletLimit

/-! Derive convergence along all centered radii from the existing STANDARD
triadic mean limit and actual finite tiling, then use the literal affine source
sequence. No all-radius convergence or domain monotonicity is a premise. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open Filter
open scoped Classical Topology

def oddBlockRatio (k r : ℕ) : ℝ :=
  (((2*r+1)/k*k:ℕ):ℝ)/(2*(r:ℝ)+1)

theorem oddBlockRatio_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (oddBlockRatio k) atTop (𝓝 1) := by
  have hden : Tendsto (fun r : ℕ => 2*(r:ℝ)+1) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro r
    have hr : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
    linarith
  have hbound : Tendsto (fun r : ℕ => (k:ℝ)/(2*(r:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlo (r : ℕ) : 0 ≤ 1-oddBlockRatio k r := by
    have hm := Nat.div_mul_le_self (2*r+1) k
    have hmR : (((2*r+1)/k*k:ℕ):ℝ) ≤ 2*(r:ℝ)+1 := by exact_mod_cast hm
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : (0:ℝ) < 2*(r:ℝ)+1)).mpr hmR
  have hhi (r : ℕ) : 1-oddBlockRatio k r ≤ (k:ℝ)/(2*(r:ℝ)+1) := by
    let n := 2*r+1
    let m := n/k*k
    have hNat : n ≤ m+k := by
      have hmod := Nat.mod_lt n hk
      have hs : n%k+m = n := by
        simpa only [m,Nat.mul_comm k (n/k)] using Nat.mod_add_div n k
      omega
    have hR : (n:ℝ) ≤ (m:ℝ)+(k:ℝ) := by exact_mod_cast hNat
    have hn : (0:ℝ) < (n:ℝ) := by dsimp [n]; positivity
    have heq : 1-(m:ℝ)/(n:ℝ) = ((n:ℝ)-(m:ℝ))/(n:ℝ) := by
      field_simp [hn.ne']
      <;> ring
    have hb : 1-(m:ℝ)/(n:ℝ) ≤ (k:ℝ)/(n:ℝ) := by
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith) hn.le
    simpa only [oddBlockRatio,m,n,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hb
  have hzero := squeeze_zero hlo hhi hbound
  have ht : Tendsto (fun r : ℕ => 1-(1-oddBlockRatio k r)) atTop (𝓝 ((1:ℝ)-0)) :=
    tendsto_const_nhds.sub hzero
  have heq : (fun r : ℕ => 1-(1-oddBlockRatio k r)) = oddBlockRatio k := by
    funext r
    ring
  rw [heq] at ht
  simpa only [sub_zero] using ht

theorem oddBlockRemainder_tendsto (k : ℕ) (hk : 0 < k) (d : ℕ) :
    Tendsto (fun r : ℕ => 1-(oddBlockRatio k r)^d) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℕ => 1-(oddBlockRatio k r)^d) atTop (𝓝 ((1:ℝ)-1^d)) :=
    tendsto_const_nhds.sub ((oddBlockRatio_tendsto k hk).pow d)
  simpa only [one_pow,sub_self] using h

/-- The existing triadic input implies the actual FULL cube means converge
along ALL radii. The block radius is chosen before the target-radius cutoff. -/
theorem annealedFull_centeredBox_tendsto {d : ℕ} (i : Fin d) {κ : ℝ → ℝ}
    (hlimit : TriadicDirichletLimitInput d i κ) (p : unitInterval)
    (hp : criticalPoint d < p) :
    Tendsto (fun r : ℕ => annealedFull (centeredBox d r) i (p:ℝ)) atTop (𝓝 (κ (p:ℝ))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun r => ha.trans_le (triadic_limit_le_full_cube i hlimit p hp r))
  · intro b hb
    obtain ⟨j,hj⟩ := ((hlimit p hp 0).eventually (gt_mem_nhds hb)).exists
    let s := triadicCubeRadius 0 j
    have hgap : 0 < b-annealedFull (centeredBox d s) i (p:ℝ) := sub_pos.mpr hj
    have he := (oddBlockRemainder_tendsto (2*s+1) (by omega) d).eventually (gt_mem_nhds hgap)
    filter_upwards [he,eventually_ge_atTop s] with r herr hrs
    have hc := annealedFull_centeredCube_block_comparison i p r s (by omega)
    change annealedFull (centeredBox d r) i (p:ℝ) ≤
      annealedFull (centeredBox d s) i (p:ℝ)+(1-(oddBlockRatio (2*s+1) r)^d) at hc
    linarith

/-- The Section10 limiting reduction now uses only the EXISTING standard
triadic input and actual eventual affine-box flow budgets; it does not ask for
an additional convergence hypothesis on that affine sequence. -/
theorem coefficient_cubic_lower_of_triadic_affine_budgets {d : ℕ} (i : Fin d)
    {κ : ℝ → ℝ} (hlimit : TriadicDirichletLimitInput d i κ)
    (p : unitInterval) (hp : criticalPoint d < p) {t : ℕ} (ht : 1 ≤ t) (r : ℕ)
    {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hbudget : ∀ᶠ M : ℕ in atTop, cubeFlowBudget p i (chemicalCoarseRadius M t r) a C) :
    (a^2/C)*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ κ (p:ℝ) := by
  have hmean := (annealedFull_centeredBox_tendsto i hlimit p hp).comp
    (chemicalCoarseRadius_tendsto ht r)
  exact coefficient_cubic_lower_of_flow_budgets p i hp
    (fun M => chemicalCoarseRadius M t r) ha hC hmean hbudget

end NearCritical.Section10
