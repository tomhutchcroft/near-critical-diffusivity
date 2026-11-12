module

public import NearCritical.AppendixBoxTwoPointLower
public import NearCritical.AppendixTwoPointBridge

/-! Expectation-level reduction for `lem.err_cluster` (main.tex ~6657).

The source proof of `lem.err_cluster` opens by taking the expectation of `E_cluster(𝔠,r)` and
rewriting it, by linearity, as a double sum over `(w ∈ F, v ∈ Q)` of the probability that both
`w` and `v` lie in the cluster of `x`, weighted by `max(r,|w-v|)^{2-d}`. This file formalizes that
first step as a DETERMINISTIC finite-sum rearrangement over `Q.powerset`: it does not touch the BK
decomposition or the two-point pointwise bounds (those remain the probabilistic/(A)-conditional
content). It consumes the `appendixBoxClusterMean` / `appendixBoxErrCluster` definitions
read-only. -/
@[expose] public section
namespace NearCritical
open scoped BigOperators
open MeasureTheory

/-- Fubini/linearity reduction for `lem.err_cluster`: the cluster-mean of the double cluster-sum
`E_cluster` equals a double sum over `(w ∈ F, v ∈ Q)` weighted by the finite "both `w,v` in the
cluster of `x`" probability `∑_{C ∋ w,v} P[clust = C]`, i.e.
`E[E_cluster] = ∑_{w∈F}∑_{v∈Q} P[w,v ∈ 𝔠]·max(r,|w-v|)^{2-d}` (the first display of the source
err_cluster proof). A deterministic finite-sum rearrangement over `Q.powerset`; the measure values
enter only as real coefficients, so no BK/(A) content is used here. -/
theorem appendixBoxClusterMean_errCluster_eq {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (r : ℕ) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrCluster C F r)
      = ∑ w ∈ F, ∑ v ∈ Q,
          (∑ C ∈ Q.powerset.filter (fun C => w ∈ C ∧ v ∈ C),
            (percolation d p).real {ω | finiteBoxCluster ω Q x = C})
          * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ)) := by
  have hinner : ∀ C ∈ Q.powerset,
      ∑ w ∈ C ∩ F, ∑ v ∈ C, (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))
        = ∑ w ∈ F, ∑ v ∈ Q,
            (if w ∈ C ∧ v ∈ C then (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ)) else 0) := by
    intro C hC
    rw [Finset.mem_powerset] at hC
    have hQC : Q ∩ C = C := Finset.inter_eq_right.mpr hC
    rw [show C ∩ F = F ∩ C from Finset.inter_comm C F, ← Finset.sum_ite_mem]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ C
    · simp only [hw, true_and, ite_true, Finset.sum_ite_mem, hQC]
    · simp only [hw, false_and, ite_false, Finset.sum_const_zero]
  have hstep : ∀ C ∈ Q.powerset,
      (percolation d p).real {ω | finiteBoxCluster ω Q x = C} * appendixBoxErrCluster C F r
        = ∑ w ∈ F, ∑ v ∈ Q,
            (if w ∈ C ∧ v ∈ C then
              (percolation d p).real {ω | finiteBoxCluster ω Q x = C}
              * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ)) else 0) := by
    intro C hC
    simp only [appendixBoxErrCluster]
    rw [hinner C hC, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [mul_ite, mul_zero]
  simp only [appendixBoxClusterMean]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter, ← Finset.sum_mul]

/-- Measure bridge: the finite powerset sum of cluster-event probabilities over clusters containing
both `w` and `v` equals the probability that both `w,v` lie in the cluster of `x` (needs `x ∈ Q`).
The `{clust = C}` events are measurable and pairwise disjoint and their union over `{C ∋ w,v}` is
exactly `{w,v ∈ 𝔠}` (using `𝔠 ⊆ Q`), so finite additivity applies. -/
theorem appendix_clusterPairWeight_eq {d : ℕ} (p : unitInterval) (Q : Finset (Vertex d))
    (x : Vertex d) (hx : x ∈ Q) (w v : Vertex d) :
    ∑ C ∈ Q.powerset.filter (fun C => w ∈ C ∧ v ∈ C),
        (percolation d p).real {ω | finiteBoxCluster ω Q x = C}
      = (percolation d p).real
          {ω | w ∈ finiteBoxCluster ω Q x ∧ v ∈ finiteBoxCluster ω Q x} := by
  have hmeas : ∀ C ∈ Q.powerset.filter (fun C => w ∈ C ∧ v ∈ C),
      MeasurableSet {ω : Configuration d | finiteBoxCluster ω Q x = C} :=
    fun C _ => measurableSet_clusterReveal_event Q C x hx
  have hpd : (↑(Q.powerset.filter (fun C => w ∈ C ∧ v ∈ C)) :
        Set (Finset (Vertex d))).PairwiseDisjoint
      (fun C => {ω : Configuration d | finiteBoxCluster ω Q x = C}) := by
    intro C _ C' _ hne
    simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
    intro ω hωC hωC'
    exact hne (hωC.symm.trans hωC')
  rw [← measureReal_biUnion_finset hpd hmeas (fun _ _ => measure_ne_top _ _)]
  congr 1
  ext ω
  simp only [Set.mem_iUnion₂, Finset.mem_filter, Finset.mem_powerset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, ⟨_, hwC, hvC⟩, hcl⟩
    rw [← hcl] at hwC hvC
    exact ⟨hwC, hvC⟩
  · rintro ⟨hw, hv⟩
    exact ⟨finiteBoxCluster ω Q x, ⟨finiteBoxCluster_subset ω Q x, hw, hv⟩, rfl⟩

/-- Expectation of `E_cluster` as a double sum of joint cluster-membership probabilities
(`x ∈ Q`): combines the Fubini reduction `appendixBoxClusterMean_errCluster_eq` with the measure
bridge `appendix_clusterPairWeight_eq`. After this, only the probabilistic/(A)-conditional content
remains — identifying `{w,v ∈ 𝔠}` with the joint connection event (`mem_finiteBoxCluster`), the BK
tree bound, and the box two-point pointwise bounds — before the deterministic lattice sums close it. -/
theorem appendixBoxClusterMean_errCluster_eq_prob {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) (r : ℕ) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrCluster C F r)
      = ∑ w ∈ F, ∑ v ∈ Q,
          (percolation d p).real {ω | w ∈ finiteBoxCluster ω Q x ∧ v ∈ finiteBoxCluster ω Q x}
          * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ)) := by
  rw [appendixBoxClusterMean_errCluster_eq]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  rw [appendix_clusterPairWeight_eq p Q x hx w v]

/-- Expectation of `E_cluster` as a double sum of joint `Q`-restricted connection probabilities
(`x ∈ Q`, `F ⊆ Q`): identifies `{w,v ∈ 𝔠}` with the joint connection event `{x ↔_Q w ∧ x ↔_Q v}`
via `mem_finiteBoxCluster`. This lands the expectation-level reduction at the exact input of the BK
tree bound `P[x↔w, x↔v] ≤ ∑_u P[x↔u]P[u↔w]P[u↔v]`, which (with the (A)-conditional two-point
pointwise bounds) is all that separates this from the deterministic lattice sums in
`AppendixErrBoundary`. -/
theorem appendixBoxClusterMean_errCluster_eq_conn {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) (r : ℕ) (hFQ : F ⊆ Q) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrCluster C F r)
      = ∑ w ∈ F, ∑ v ∈ Q,
          (percolation d p).real {ω |
              (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
            ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v}
          * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ)) := by
  rw [appendixBoxClusterMean_errCluster_eq_prob p Q F x hx r]
  apply Finset.sum_congr rfl
  intro w hwF
  apply Finset.sum_congr rfl
  intro v hvQ
  have hset : {ω : Configuration d |
        w ∈ finiteBoxCluster ω Q x ∧ v ∈ finiteBoxCluster ω Q x}
      = {ω | (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
            ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_finiteBoxCluster]
    constructor
    · rintro ⟨⟨_, hw⟩, ⟨_, hv⟩⟩; exact ⟨hw, hv⟩
    · rintro ⟨hw, hv⟩; exact ⟨⟨hFQ hwF, hw⟩, ⟨hvQ, hv⟩⟩
  rw [hset]

/-- Final assembly of `lem.err_cluster` (conditional form): given the per-`w` two-point sum bound
`hperW` (the source's `∑_{v∈Q} P[x↔w,x↔v]·max(r,|w-v|)^{2-d} ≲ h^{-d}r^{6-d}` uniform over `w∈F`,
which the paper derives from the BK tree bound, the (A)-conditional box two-point pointwise bounds,
and the convolution estimate `conv_pointwise_le`), the expectation of `E_cluster` is `≤ |F|·B`.
Chaining the source's `|F| ∼ h^{d-1}` with `B ∼ h^{-d}r^{6-d}` then gives the `∼ n^{-1}r^{6-d}` of
the lemma. This isolates ALL genuinely cited/(A)-conditional content into the single hypothesis
`hperW`; everything else — the Fubini/measure reduction and the `|F|`-counting — is verified here. -/
theorem appendixBoxClusterMean_errCluster_bound {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) (r : ℕ) (hFQ : F ⊆ Q) (B : ℝ)
    (hperW : ∀ w ∈ F,
      ∑ v ∈ Q, (percolation d p).real {ω |
            (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
          ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v}
        * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ)) ≤ B) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrCluster C F r) ≤ (F.card : ℝ) * B := by
  rw [appendixBoxClusterMean_errCluster_eq_conn p Q F x hx r hFQ]
  calc ∑ w ∈ F, ∑ v ∈ Q, (percolation d p).real {ω |
            (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
          ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x v}
          * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))
      ≤ ∑ _w ∈ F, B := Finset.sum_le_sum hperW
    _ = (F.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Fubini/linearity reduction for `lem.err_boundary`: the cluster-mean of `E_boundary` (the
off-diagonal double sum over `F∩𝔠`) equals a double sum over `(w∈F, w'∈F.erase w)` weighted by the
finite "both in 𝔠" probability. Deterministic finite-sum rearrangement over `Q.powerset`. -/
theorem appendixBoxClusterMean_errBoundary_eq {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (r : ℕ) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrBoundary C F r)
      = ∑ w ∈ F, ∑ w' ∈ F.erase w,
          (∑ C ∈ Q.powerset.filter (fun C => w ∈ C ∧ w' ∈ C),
            (percolation d p).real {ω | finiteBoxCluster ω Q x = C})
          * (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ)) := by
  have hinner : ∀ C ∈ Q.powerset,
      ∑ w ∈ C ∩ F, ∑ w' ∈ (C ∩ F).erase w,
          (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ))
        = ∑ w ∈ F, ∑ w' ∈ F.erase w,
            (if w ∈ C ∧ w' ∈ C then
              (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ)) else 0) := by
    intro C _
    rw [show C ∩ F = F ∩ C from Finset.inter_comm C F, ← Finset.sum_ite_mem]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ C
    · simp only [hw, true_and, ite_true]
      rw [show (F ∩ C).erase w = (F.erase w) ∩ C from by
            ext a; simp only [Finset.mem_erase, Finset.mem_inter]; tauto,
          ← Finset.sum_ite_mem]
    · simp only [hw, false_and, ite_false, Finset.sum_const_zero]
  have hstep : ∀ C ∈ Q.powerset,
      (percolation d p).real {ω | finiteBoxCluster ω Q x = C} * appendixBoxErrBoundary C F r
        = ∑ w ∈ F, ∑ w' ∈ F.erase w,
            (if w ∈ C ∧ w' ∈ C then
              (percolation d p).real {ω | finiteBoxCluster ω Q x = C}
              * (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ)) else 0) := by
    intro C hC
    simp only [appendixBoxErrBoundary]
    rw [hinner C hC, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w' _
    rw [mul_ite, mul_zero]
  simp only [appendixBoxClusterMean]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w' _
  rw [← Finset.sum_filter, ← Finset.sum_mul]

/-- `E_boundary` expectation as a double sum of joint `Q`-connection probabilities (`x∈Q`, `F⊆Q`):
reuses the measure bridge `appendix_clusterPairWeight_eq` and `mem_finiteBoxCluster`. -/
theorem appendixBoxClusterMean_errBoundary_eq_conn {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) (r : ℕ) (hFQ : F ⊆ Q) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrBoundary C F r)
      = ∑ w ∈ F, ∑ w' ∈ F.erase w,
          (percolation d p).real {ω |
              (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
            ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w'}
          * (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ)) := by
  rw [appendixBoxClusterMean_errBoundary_eq]
  apply Finset.sum_congr rfl
  intro w hwF
  apply Finset.sum_congr rfl
  intro w' hw'
  rw [appendix_clusterPairWeight_eq p Q x hx w w']
  have hw'F : w' ∈ F := Finset.mem_of_mem_erase hw'
  have hset : {ω : Configuration d |
        w ∈ finiteBoxCluster ω Q x ∧ w' ∈ finiteBoxCluster ω Q x}
      = {ω | (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
            ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w'} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_finiteBoxCluster]
    constructor
    · rintro ⟨⟨_, hw⟩, ⟨_, hv⟩⟩; exact ⟨hw, hv⟩
    · rintro ⟨hw, hv⟩; exact ⟨⟨hFQ hwF, hw⟩, ⟨hFQ hw'F, hv⟩⟩
  rw [hset]

/-- Final assembly of `lem.err_boundary` (conditional form): given the per-`w` two-point sum bound
`hperW` over `F.erase w`, the expectation of `E_boundary` is `≤ |F|·B`. Isolates all cited/(A)
content into `hperW`. -/
theorem appendixBoxClusterMean_errBoundary_bound {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) (r : ℕ) (hFQ : F ⊆ Q) (B : ℝ)
    (hperW : ∀ w ∈ F,
      ∑ w' ∈ F.erase w, (percolation d p).real {ω |
            (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
          ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w'}
        * (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ)) ≤ B) :
    appendixBoxClusterMean p Q x (fun C => appendixBoxErrBoundary C F r) ≤ (F.card : ℝ) * B := by
  rw [appendixBoxClusterMean_errBoundary_eq_conn p Q F x hx r hFQ]
  calc ∑ w ∈ F, ∑ w' ∈ F.erase w, (percolation d p).real {ω |
            (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w
          ∧ (restrictedGraph ω (Q : Set (Vertex d))).Reachable x w'}
          * (max (r : ℝ) (latticeDistance w w')) ^ ((4 : ℝ) - (d : ℝ))
      ≤ ∑ _w ∈ F, B := Finset.sum_le_sum hperW
    _ = (F.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

open NearCritical.AppendixVariance in
/-- Kernel regularization bridge: the paper's error-sum kernel `max(r,|w-v|)^{2-d}` (real `rpow`,
real distance `latticeDistance`) is bounded by `2^{d-2}` times the regularized kernel
`1/max(r,|w-v|+1)^{d-2}` (nat power) that the per-`w` derivation `perW_bound` produces. Holds for
ALL lattice points (no distinctness needed), since `max(r,m+1) ≤ 2·max(r,m)` whenever `r ≥ 1`.
This is the one deterministic glue step between `perW_bound`'s output and the real
`appendixBoxErrCluster` kernel; it needs no probabilistic input. -/
theorem kernel_reg_bridge {d : ℕ} (hd : 2 ≤ d) {r : ℕ} (hr : 1 ≤ r) (w v : Vertex d) :
    (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))
      ≤ 2 ^ (d - 2) * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)) := by
  rw [← linfDist_cast_eq_latticeDistance]
  set m := linfDist w v with hm
  set a : ℝ := max (r : ℝ) (m : ℝ) with ha
  set b : ℝ := max (r : ℝ) ((m + 1 : ℕ) : ℝ) with hb
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have har : (r : ℝ) ≤ a := le_max_left _ _
  have ham : (m : ℝ) ≤ a := le_max_right _ _
  have ha1 : (1 : ℝ) ≤ a := le_trans hrr har
  have hb1 : (1 : ℝ) ≤ b := le_trans hrr (le_max_left _ _)
  have hba : b ≤ 2 * a := by
    apply max_le
    · linarith
    · have : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [this]; linarith
  have hapos : (0 : ℝ) < a ^ (d - 2) := by positivity
  have hbpos : (0 : ℝ) < b ^ (d - 2) := by positivity
  have hbpow : b ^ (d - 2) ≤ 2 ^ (d - 2) * a ^ (d - 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hba (d - 2)
  have hexp : (2 : ℝ) - (d : ℝ) = -(((d - 2 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hd]; push_cast; ring
  rw [hexp, Real.rpow_neg (by linarith : (0 : ℝ) ≤ a), Real.rpow_natCast,
      mul_one_div, inv_eq_one_div, div_le_div_iff₀ hapos hbpos, one_mul]
  exact hbpow

open NearCritical.AppendixVariance in
/-- Sum-level kernel bridge: lifts `kernel_reg_bridge` through a nonnegative weight `P` over the box.
If the regularized per-`w` sum (the form `perW_bound` outputs) is `≤ B`, then the real-exponent
per-`w` sum (the form `appendixBoxClusterMean_errCluster_bound`'s `hperW` consumes) is `≤ 2^{d-2}·B`.
This is the last deterministic step making `hperW` follow from `perW_bound` plus the cited
`hBK`/`hApt`; it introduces no probabilistic hypothesis. -/
theorem sum_real_kernel_le_of_reg {d : ℕ} (hd : 2 ≤ d) {r : ℕ} (hr : 1 ≤ r)
    (w c : Vertex d) (K : ℕ) (P : Vertex d → ℝ) (hP : ∀ v, 0 ≤ P v) (B : ℝ)
    (hreg : ∑ v ∈ linfBall c (K : ℤ),
        P v * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)) ≤ B) :
    ∑ v ∈ linfBall c (K : ℤ),
        P v * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))
      ≤ 2 ^ (d - 2) * B := by
  calc ∑ v ∈ linfBall c (K : ℤ),
          P v * (max (r : ℝ) (latticeDistance w v)) ^ ((2 : ℝ) - (d : ℝ))
      ≤ ∑ v ∈ linfBall c (K : ℤ),
          P v * (2 ^ (d - 2) * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))) := by
        apply Finset.sum_le_sum
        intro v _
        exact mul_le_mul_of_nonneg_left (kernel_reg_bridge hd hr w v) (hP v)
    _ = 2 ^ (d - 2) * ∑ v ∈ linfBall c (K : ℤ),
          P v * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun v _ => by ring)
    _ ≤ 2 ^ (d - 2) * B := mul_le_mul_of_nonneg_left hreg (by positivity)

end NearCritical
