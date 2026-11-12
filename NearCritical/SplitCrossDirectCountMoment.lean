module

public import NearCritical.SplitCrossDirectMoment

/-! Moments of restricted cluster counts (item B of the direct proof of
`SplitCrossInput`, closed form).

* `gammaN n k`: the integer recursion `γ(n+1,k) = [k=1] + Σ_{0<j<k} C(k,j) γ(n,j) γ(n,k-j)`.
* `gN_eq`: `gN m B n k = γ(n,k) m^k B^(k-1)`.
* `countIn D Y u ω`: the number of points of `Y` joined to `u` inside `D`.
* `integral_countIn_pow_le_sum`: `E[countIn^|ι|] ≤ Σ_{y ∈ Y^ι} P[u ↔ y_i in D ∀ i]`.
* **`countIn_moment_le`**: for `n ≥ 1`,
  `E[countIn^n] ≤ γ(n,n) m^n B^(n-1)`
  whenever `Σ_{v∈Y} P[u' ↔ v in D] ≤ m` and `Σ_{w∈D} P[u' ↔ w in D] ≤ B` for
  every `u'`.

With `B ≍ t^2` this gives `E[W^n] ≲ t^(4n-2)` for an interior box (`m ≍ t^2`)
and `E[V^n] ≲ t^(2n-2)` for a boundary face (`m ≍ 1`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory
open scoped Classical BigOperators

variable {d : ℕ}

/-- Integer coefficients of the moment recursion. -/
def gammaN : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, k => (if k = 1 then 1 else 0) +
      ∑ j ∈ Finset.Ico 1 k, k.choose j * gammaN n j * gammaN n (k - j)

theorem gammaN_succ (n k : ℕ) :
    gammaN (n + 1) k = (if k = 1 then 1 else 0) +
      ∑ j ∈ Finset.Ico 1 k, k.choose j * gammaN n j * gammaN n (k - j) := rfl

theorem gN_eq (m B : ℝ) : ∀ n k : ℕ, gN m B n k = (gammaN n k : ℝ) * m ^ k * B ^ (k - 1)
  | 0, k => by
    show (0 : ℝ) = ((0 : ℕ) : ℝ) * m ^ k * B ^ (k - 1)
    simp
  | n+1, k => by
    rw [gN_succ, gammaN_succ]
    push_cast
    rw [add_mul, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · split_ifs with hk
      · subst hk
        simp
      · simp
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Ico] at hj
      rw [gN_eq m B n j, gN_eq m B n (k - j)]
      have hmpow : m ^ j * m ^ (k - j) = m ^ k := by
        rw [← pow_add]
        congr 1
        omega
      have hBpow : B * (B ^ (j - 1) * B ^ (k - j - 1)) = B ^ (k - 1) := by
        rw [← pow_add, ← pow_succ']
        congr 1
        omega
      calc B * ((k.choose j : ℝ) * ((gammaN n j : ℝ) * m ^ j * B ^ (j - 1)) *
            ((gammaN n (k - j) : ℝ) * m ^ (k - j) * B ^ (k - j - 1)))
          = (k.choose j : ℝ) * (gammaN n j : ℝ) * (gammaN n (k - j) : ℝ) *
              (m ^ j * m ^ (k - j)) * (B * (B ^ (j - 1) * B ^ (k - j - 1))) := by ring
        _ = _ := by rw [hmpow, hBpow]

/-- Number of points of `Y` joined to `u` inside `D`. -/
def countIn (D : Set (Vertex d)) (Y : Finset (Vertex d)) (u : Vertex d)
    (ω : Configuration d) : ℝ :=
  ∑ v ∈ Y, (connectionToSetEvent D u {v}).indicator (fun _ => (1 : ℝ)) ω

theorem integral_countIn_pow_le_sum {ι : Type*} [Fintype ι] (p : unitInterval)
    (D : Set (Vertex d)) (Y : Finset (Vertex d)) (u : Vertex d) :
    ∫ ω, countIn D Y u ω ^ Fintype.card ι ∂percolation d p ≤
      ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), (percolation d p).real {ω | ∀ i : ι,
        (restrictedGraph ω D).Reachable u (y i)} := by
  have hpow : ∀ ω, countIn D Y u ω ^ Fintype.card ι =
      ∑ y ∈ Fintype.piFinset (fun _ : ι => Y),
        ∏ i : ι, (connectionToSetEvent D u {y i}).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_univ_sum (fun _ : ι => Y)
      (fun (_ : ι) (v : Vertex d) => (connectionToSetEvent D u {v}).indicator (fun _ => (1 : ℝ)) ω)
  have hprod : ∀ (y : ι → Vertex d) (ω : Configuration d),
      (∏ i : ι, (connectionToSetEvent D u {y i}).indicator (fun _ => (1 : ℝ)) ω) =
        (⋂ i : ι, connectionToSetEvent D u {y i}).indicator (fun _ => (1 : ℝ)) ω := by
    intro y ω
    by_cases h : ω ∈ ⋂ i : ι, connectionToSetEvent D u {y i}
    · rw [Set.indicator_of_mem h]
      exact Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (Set.mem_iInter.mp h i) _)
    · rw [Set.indicator_of_notMem h]
      obtain ⟨i, hi⟩ := not_forall.mp (fun hall => h (Set.mem_iInter.mpr hall))
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  have hmeas : ∀ y : ι → Vertex d,
      MeasurableSet (⋂ i : ι, connectionToSetEvent D u {y i}) :=
    fun y => MeasurableSet.iInter (fun i => measurableSet_connectionToSetEvent D u {y i})
  simp_rw [hpow, hprod]
  rw [integral_finset_sum _ (fun y _ => (integrable_const (1 : ℝ)).indicator (hmeas y))]
  refine Finset.sum_le_sum (fun y _ => ?_)
  have h3 : (∫ ω, (⋂ i : ι, connectionToSetEvent D u {y i}).indicator (fun _ => (1 : ℝ)) ω
      ∂percolation d p) = (percolation d p).real (⋂ i : ι, connectionToSetEvent D u {y i}) :=
    integral_indicator_one (hmeas y)
  rw [h3]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω i
  obtain ⟨_, v, hv, _, hreach⟩ := Set.mem_iInter.mp hω i
  rw [Set.mem_singleton_iff] at hv
  exact hv ▸ hreach

/-- **Moment bound for restricted cluster counts.** -/
theorem countIn_moment_le (n : ℕ) (hn : 0 < n) (p : unitInterval) (Dfin Y : Finset (Vertex d))
    (hY : 0 < Y.card) {m B : ℝ} (hm0 : 0 ≤ m) (hB0 : 0 ≤ B)
    (hm : ∀ u, ∑ v ∈ Y, (percolation d p).real
      (connectionToSetEvent (Dfin : Set (Vertex d)) u {v}) ≤ m)
    (hB : ∀ u, ∑ w ∈ Dfin, (percolation d p).real
      (connectionToSetEvent (Dfin : Set (Vertex d)) u {w}) ≤ B)
    {u : Vertex d} (hu : u ∈ Dfin) :
    ∫ ω, countIn (Dfin : Set (Vertex d)) Y u ω ^ n ∂percolation d p ≤
      (gammaN n n : ℝ) * m ^ n * B ^ (n - 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 := integral_countIn_pow_le_sum (ι := Fin n) p (Dfin : Set (Vertex d)) Y u
  have h2 := sum_connections_le (ι := Fin n) p Dfin Y hY hm0 hB0 hm hB hu
  rw [Fintype.card_fin] at h1 h2
  rw [← gN_eq]
  exact h1.trans h2

end NearCritical.SplitCrossDirect
end
