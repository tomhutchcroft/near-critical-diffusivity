module
public import NearCritical.AppendixBoxTwoPointLower

/-! Conditional lem.box_twopoint_lower (main.tex 6616) at EVERY scale `n ≥ 1`, for
`x` on a negative face `{z i = -n}` of `Λ_n`. Large scales `α n ≥ 16 r(α)` use
`appendix_box_twopoint_lower_large`. The finitely many remaining scales use the
all-open finite-energy bound `centeredBox_connection_lower_allOpen`, minimized over
`n < N`, together with `n^{1-d} ≤ 1`. The explicit inputs are exactly those of
`appendix_box_twopoint_lower_large`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Extend a large-scale negative-face estimate to every scale by the
all-open bound on the finitely many small cubes. -/
theorem appendix_box_twopoint_lower_negFace_of_large {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) {α β : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β)
    {cL : ℝ} (hcL : 0 < cL) (r : ℕ)
    (hlarge : ∀ (i : Fin d) (n : ℕ) (x y : Vertex d),
      16 * (r : ℝ) ≤ β * (n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      cL * (n : ℝ) ^ ((1 : ℝ) - (d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (centeredBox d n : Set (Vertex d)) x {y})) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d), 1 ≤ n →
      x i = -(n : ℤ) → (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      c*(n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  obtain ⟨hp0,hp1⟩ := criticalPoint_interior_of_twoPointAsymptotics (by omega : 2 < d)
    ⟨0,by omega⟩ asymp
  let μ : ℝ := min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ))
  have hμ : 0 < μ := lt_min hp0 (by linarith)
  let N : ℕ := Nat.ceil (16*(r : ℝ)/β)+1
  have hNne : (Finset.range N).Nonempty := ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
  let small : ℕ → ℝ := fun k => μ^(internalBondSet (centeredBox d k)).card
  let cS : ℝ := (Finset.range N).inf' hNne small
  have hcS : 0 < cS := (Finset.lt_inf'_iff hNne).mpr (fun k _ => pow_pos hμ _)
  refine ⟨min cL cS,lt_min hcL hcS,?_⟩
  intro i n x y hn hxi hx hy
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow1 : (n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
  have hpow0 : 0 ≤ (n : ℝ)^((1 : ℝ)-(d : ℝ)) := Real.rpow_nonneg (by linarith) _
  by_cases hbig : 16*(r : ℝ) ≤ β*(n : ℝ)
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hpow0).trans
      (hlarge i n x y hbig hxi hx hy)
  · push_neg at hbig
    have hnN : n ∈ Finset.range N := by
      apply Finset.mem_range.mpr
      have h1 : (n : ℝ) < 16*(r : ℝ)/β := by
        rw [lt_div_iff₀ hβ0]
        linarith
      have h2 : 16*(r : ℝ)/β ≤ (Nat.ceil (16*(r : ℝ)/β) : ℝ) := Nat.le_ceil _
      have h3 : (n : ℝ) < (Nat.ceil (16*(r : ℝ)/β) : ℝ) := lt_of_lt_of_le h1 h2
      have h4 : n < Nat.ceil (16*(r : ℝ)/β) := by exact_mod_cast h3
      show n < Nat.ceil (16*(r : ℝ)/β)+1
      omega
    have hxbox : x ∈ centeredBox d n := by
      rw [mem_centeredBox]
      intro j
      by_cases hj : j = i
      · rw [hj,hxi]
        constructor <;> omega
      · have h1 := abs_le.mp (hx j hj)
        have h2 : -(n : ℝ) ≤ (x j : ℝ) := by nlinarith
        have h3 : (x j : ℝ) ≤ (n : ℝ) := by nlinarith
        constructor
        · exact_mod_cast h2
        · exact_mod_cast h3
    have hybox : y ∈ centeredBox d n := by
      rw [mem_centeredBox]
      intro j
      have h1 := abs_le.mp (hy j)
      have h2 : -(n : ℝ) ≤ (y j : ℝ) := by nlinarith
      have h3 : (y j : ℝ) ≤ (n : ℝ) := by nlinarith
      constructor
      · exact_mod_cast h2
      · exact_mod_cast h3
    have hsmall := centeredBox_connection_lower_allOpen (criticalPoint d) n hxbox hybox
    have hcSn : cS ≤ small n := Finset.inf'_le small hnN
    calc min cL cS*(n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤ cS*1 :=
          mul_le_mul (min_le_right _ _) hpow1 hpow0 hcS.le
      _ = cS := mul_one _
      _ ≤ small n := hcSn
      _ ≤ _ := hsmall

theorem appendix_box_twopoint_lower_negFace {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hreg : ∃ creg : ℝ, 0 < creg ∧ ∀ (i : Fin d) (n : ℕ) (x : Vertex d),
      1 ≤ n → 16 ≤ α*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      creg/(n : ℝ) ≤ appendixBoxClusterMean (criticalPoint d)
        (appendixBoxQ n (Nat.floor (α*(n : ℝ)/8)) i x) x
        (fun C => ((C ∩ appendixBoxF n (Nat.floor (α*(n : ℝ)/8)) i x).card : ℝ)))
    (herr : ∃ Kerr : ℝ, 0 ≤ Kerr ∧ ∀ (i : Fin d) (n r : ℕ) (x : Vertex d),
      1 ≤ n → 1 ≤ r → 16 ≤ α*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      appendixBoxClusterMean (criticalPoint d)
          (appendixBoxQ n (Nat.floor (α*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrCluster C (appendixBoxF n (Nat.floor (α*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ) ∧
      appendixBoxClusterMean (criticalPoint d)
          (appendixBoxQ n (Nat.floor (α*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrBoundary C (appendixBoxF n (Nat.floor (α*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d), 1 ≤ n →
      x i = -(n : ℤ) → (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      c*(n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  obtain ⟨cL, hcL, r, _, hlarge⟩ :=
    appendix_box_twopoint_lower_large hd asymp lower hα0 hα1 hreg herr
  exact appendix_box_twopoint_lower_negFace_of_large hd asymp hα0 hα0 hcL r hlarge

end NearCritical
