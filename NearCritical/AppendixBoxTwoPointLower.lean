module
public import NearCritical.AppendixBoxFaceBudget
public import NearCritical.CriticalPointInterior

/-! Conditional assembly of lem.box_twopoint_lower (main.tex 6616-6735) for `x` on the
face `{z i = -n}` of `Λ_n`.

Explicit inputs, stated as expectations over the ACTUAL cluster `C` of `x` in
`Q(x) = appendixBoxQ n h i x`, with `h = ⌊α n/8⌋`:
* `lem.boundary_regularity`, eq.boundary_0_mean_segment: `E|C ∩ F| ≥ c_reg / n`;
* `lem.err_cluster`: `E[E_cluster(C,r)] ≤ K r^{6-d} / n`;
* `lem.err_boundary`: `E[E_boundary(C,r)] ≤ K r^{6-d} / n`;
* the cited CH20 input `RestrictedRectangleLowerInput` and assumption (A).
None of these is discharged here. The proof combines
`appendix_box_cluster_sum_lower` (eq.lower_step1) with `appendix_box_face_avoid_lower`,
splits off the diagonal `w' = w` term of the boundary sum (which the source omits),
and fixes `r = r(α)`. The finitely many small scales use
`centeredBox_connection_lower_allOpen`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Source `E_cluster(C, r)` (main.tex ~6660): `Σ_{w ∈ C∩F} Σ_{v ∈ C} max(r,|w-v|)^{2-d}`. -/
def appendixBoxErrCluster {d : ℕ} (C F : Finset (Vertex d)) (r : ℕ) : ℝ :=
  ∑ w ∈ C ∩ F, ∑ v ∈ C, (max (r : ℝ) (latticeDistance w v))^((2 : ℝ)-(d : ℝ))

/-- Source `E_boundary(C, r)` (main.tex ~6650): `Σ_{w ≠ w' ∈ C∩F} max(r,|w-w'|)^{4-d}`. -/
def appendixBoxErrBoundary {d : ℕ} (C F : Finset (Vertex d)) (r : ℕ) : ℝ :=
  ∑ w ∈ C ∩ F, ∑ w' ∈ (C ∩ F).erase w, (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ))

/-- Expectation over the actual cluster of `x` in `Q`, of a function of the cluster. -/
def appendixBoxClusterMean {d : ℕ} (p : unitInterval) (Q : Finset (Vertex d)) (x : Vertex d)
    (f : Finset (Vertex d) → ℝ) : ℝ :=
  ∑ C ∈ Q.powerset, (percolation d p).real {ω | finiteBoxCluster ω Q x = C} * f C

/-- The diagonal-inclusive boundary sum splits as `E_boundary + r^{4-d} |C ∩ F|`. -/
lemma appendix_box_boundary_diagonal_split {d : ℕ} (C F : Finset (Vertex d)) (r : ℕ)
    (hr : 1 ≤ r) :
    ∑ w ∈ C ∩ F, ∑ w' ∈ C ∩ F, (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)) =
      appendixBoxErrBoundary C F r + ((C ∩ F).card : ℝ)*(r : ℝ)^((4 : ℝ)-(d : ℝ)) := by
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdiag (w : Vertex d) : (max (r : ℝ) (latticeDistance w w))^((4 : ℝ)-(d : ℝ)) =
      (r : ℝ)^((4 : ℝ)-(d : ℝ)) := by
    have h0 : latticeDistance w w = 0 := by
      change dist (vertexReal w) (vertexReal w) = 0
      exact dist_self _
    rw [h0,max_eq_left hrR]
  have hsplit (w : Vertex d) (hw : w ∈ C ∩ F) :
      ∑ w' ∈ C ∩ F, (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)) =
        (r : ℝ)^((4 : ℝ)-(d : ℝ)) +
          ∑ w' ∈ (C ∩ F).erase w, (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)) := by
    rw [← Finset.add_sum_erase _ _ hw,hdiag]
  rw [Finset.sum_congr rfl hsplit,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
  unfold appendixBoxErrBoundary
  ring

/-- For `r ≥ 1` and `d ≥ 7`, `r^{6-d} ≤ 1/r`. -/
lemma appendix_rpow_six_sub_le_inv {d : ℕ} (hd : 7 ≤ d) {r : ℝ} (hr : 1 ≤ r) :
    r^((6 : ℝ)-(d : ℝ)) ≤ 1/r := by
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)

/-- Large-scale box lower bound with separate transverse and height scales.
The errors are required only for cutoffs no larger than the exploration height. -/
theorem appendix_box_twopoint_lower_large_on_domain {d : ℕ} (hd : 7 ≤ d) (asymp : TwoPointAsymptotics d)
    (lower : RestrictedRectangleLowerInput d) {α β : ℝ} (hβ0 : 0 < β) (hβα : β ≤ α) (hα1 : α ≤ 1)
    (Qbox Fbox : ℕ → Fin d → Vertex d → Finset (Vertex d))
    (hgeometry : ∀ (i : Fin d) (n : ℕ) (x : Vertex d),
      1 ≤ n → 16 ≤ β * (n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      let Q := Qbox n i x
      let F := Fbox n i x
      let h := Nat.floor (β * (n : ℝ) / 8)
      x ∈ Q ∧ Q ⊆ centeredBox d n ∧ (∀ u ∈ Q, u i ≤ -(n : ℤ) + h) ∧ F ⊆ Q ∧
        (∀ w ∈ F, w i = -(n : ℤ) + h) ∧
        (∀ w ∈ F, ∀ j, j ≠ i → |(w j : ℝ) - (x j : ℝ)| ≤ α * (n : ℝ) / 4))
    (hreg : ∃ creg : ℝ, 0 < creg ∧ ∀ (i : Fin d) (n : ℕ) (x : Vertex d),
      1 ≤ n → 16 ≤ β*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      creg/(n : ℝ) ≤ appendixBoxClusterMean (criticalPoint d)
        (Qbox n i x) x
        (fun C => ((C ∩ Fbox n i x).card : ℝ)))
    (herr : ∃ Kerr : ℝ, 0 ≤ Kerr ∧ ∀ (i : Fin d) (n r : ℕ) (x : Vertex d),
      1 ≤ n → 1 ≤ r → r ≤ Nat.floor (β * (n : ℝ) / 8) → 16 ≤ β*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      appendixBoxClusterMean (criticalPoint d)
          (Qbox n i x) x
          (fun C => appendixBoxErrCluster C (Fbox n i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ) ∧
      appendixBoxClusterMean (criticalPoint d)
          (Qbox n i x) x
          (fun C => appendixBoxErrBoundary C (Fbox n i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ r : ℕ, 1 ≤ r ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d),
      16*(r : ℝ) ≤ β*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      c*(n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  obtain ⟨cb,K₁,K₂,hcb,hK₁,hK₂,hface⟩ := appendix_box_face_avoid_lower_on_domain hd asymp lower hβ0 hβα hα1
  obtain ⟨creg,hcreg,hreg⟩ := hreg
  obtain ⟨Kerr,hKerr,herr⟩ := herr
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hKK : 0 ≤ (K₁+K₂)*Kerr := mul_nonneg (by linarith) hKerr
  -- choose r with K₂ r^{4-d} ≤ cb/2 and (K₁+K₂) Kerr r^{6-d} ≤ cb creg/4
  have hε1pos : 0 < cb/(2*(K₂+1)) := div_pos hcb (by linarith)
  have hε2pos : 0 < cb*creg/(4*((K₁+K₂)*Kerr+1)) := div_pos (mul_pos hcb hcreg) (by linarith)
  let ε : ℝ := min (cb/(2*(K₂+1))) (cb*creg/(4*((K₁+K₂)*Kerr+1)))
  have hε : 0 < ε := lt_min hε1pos hε2pos
  let r : ℕ := Nat.ceil (1/ε)+1
  have hr1 : 1 ≤ r := Nat.le_add_left 1 _
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrε : 1/ε ≤ (r : ℝ) := by
    have h1 : 1/ε ≤ (Nat.ceil (1/ε) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (1/ε)+1 : ℕ) : ℝ) = (Nat.ceil (1/ε) : ℝ)+1 := by norm_cast
    change 1/ε ≤ ((Nat.ceil (1/ε)+1 : ℕ) : ℝ)
    rw [h2]
    linarith
  have hr6 : (r : ℝ)^((6 : ℝ)-(d : ℝ)) ≤ ε := by
    refine (appendix_rpow_six_sub_le_inv hd hrR).trans ?_
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ hε] at hrε
    linarith
  have hr6n : 0 ≤ (r : ℝ)^((6 : ℝ)-(d : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hr4 : (r : ℝ)^((4 : ℝ)-(d : ℝ)) ≤ (r : ℝ)^((6 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hrR (by linarith)
  have hK₂r : K₂*(r : ℝ)^((4 : ℝ)-(d : ℝ)) ≤ cb/2 := by
    have h1 : (r : ℝ)^((6 : ℝ)-(d : ℝ)) ≤ cb/(2*(K₂+1)) := hr6.trans (min_le_left _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    have h2 := mul_le_mul_of_nonneg_left hr4 hK₂
    nlinarith
  have hKr : ((K₁+K₂)*Kerr)*(r : ℝ)^((6 : ℝ)-(d : ℝ)) ≤ cb*creg/4 := by
    have h1 : (r : ℝ)^((6 : ℝ)-(d : ℝ)) ≤ cb*creg/(4*((K₁+K₂)*Kerr+1)) :=
      hr6.trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith
  obtain ⟨hp0,hp1⟩ := criticalPoint_interior_of_twoPointAsymptotics (by omega : 2 < d)
    ⟨0,by omega⟩ asymp
  have hc₂ : 0 < (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1)) :=
    pow_pos (lt_min hp0 (by linarith)) _
  refine ⟨(min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*(cb*creg/4),
    mul_pos hc₂ (div_pos (mul_pos hcb hcreg) (by norm_num)),r,hr1,?_⟩
  intro i n x y hn hxi hx hy
  -- scale facts
  have hβn16 : 16 ≤ β * (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) < n := by
    by_contra hn
    push_neg at hn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ0.le hn]
  have hn1 : 1 ≤ n := by
    have : (0 : ℕ) < n := by exact_mod_cast hn0
    omega
  have hβαn := mul_le_mul_of_nonneg_right hβα hn0.le
  have hrnβ : (r : ℝ) ≤ β * (n : ℝ) / 16 := by linarith
  have hrn : (r : ℝ) ≤ α * (n : ℝ) / 16 := by linarith
  have hαn1 : 1 ≤ α * (n : ℝ) := by linarith
  let h := Nat.floor (β * (n : ℝ) / 8)
  have hhle : (h : ℝ) ≤ α * (n : ℝ) / 8 := by
    have hhβ : (h : ℝ) ≤ β * (n : ℝ) / 8 :=
      Nat.floor_le (div_nonneg (mul_nonneg hβ0.le hn0.le) (by norm_num))
    linarith
  have hhge : β * (n : ℝ) / 16 ≤ (h : ℝ) := by
    have hh := Nat.lt_floor_add_one (β * (n : ℝ) / 8)
    change β * (n : ℝ) / 8 < (h : ℝ) + 1 at hh
    linarith
  have hrh : r ≤ h := by exact_mod_cast hrnβ.trans hhge
  let Q := Qbox n i x
  let F := Fbox n i x
  obtain ⟨hxQ, hQT, hQheight, hFQ, hFheight, hFwidth⟩ := hgeometry i n x hn1 hβn16 hxi hx
  have hreg' := hreg i n x hn1 hβn16 hxi hx
  obtain ⟨hEcl, hEbd⟩ := herr i n r x hn1 hr1 hrh hβn16 hxi hx
  have hstep1 := appendix_box_cluster_sum_lower (criticalPoint d) (centeredBox d n) Q F x y hQT hxQ
  -- per-cluster lower bound from the face budget
  have hnq : 0 ≤ (n : ℝ)^((2 : ℝ)-(d : ℝ)) := Real.rpow_nonneg hn0.le _
  have hperC (C : Finset (Vertex d)) (hC : C ∈ Q.powerset) :
      (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*(n : ℝ)^((2 : ℝ)-(d : ℝ))*
        ((cb-K₂*(r : ℝ)^((4 : ℝ)-(d : ℝ)))*((C ∩ F).card : ℝ) - K₁*appendixBoxErrCluster C F r
          - K₂*appendixBoxErrBoundary C F r) ≤
        ∑ w ∈ C ∩ F, (percolation d (criticalPoint d)).real
          (appendixBoxAvoidEvent (centeredBox d n) Q C (C ∩ F) y w) := by
    have hCQ : C ⊆ Q := Finset.mem_powerset.mp hC
    have hsum := Finset.sum_le_sum (fun w hw =>
      hface i n h r x y Q F hr1 hhge hhle hrn hαn1 hx hy hQT hQheight hFQ hFheight hFwidth C hCQ w hw)
    refine le_trans (le_of_eq ?_) hsum
    have hdiag := appendix_box_boundary_diagonal_split C F r hr1
    have hre : ∑ w ∈ C ∩ F, (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
        ((n : ℝ)^((2 : ℝ)-(d : ℝ))*(cb - K₁*∑ v ∈ C,
          (max (r : ℝ) (latticeDistance w v))^((2 : ℝ)-(d : ℝ)) - K₂*∑ w' ∈ C ∩ F,
          (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)))) =
        ∑ w ∈ C ∩ F, ((min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
            (n : ℝ)^((2 : ℝ)-(d : ℝ))*cb -
          (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
            (n : ℝ)^((2 : ℝ)-(d : ℝ))*K₁*∑ v ∈ C,
              (max (r : ℝ) (latticeDistance w v))^((2 : ℝ)-(d : ℝ)) -
          (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
            (n : ℝ)^((2 : ℝ)-(d : ℝ))*K₂*∑ w' ∈ C ∩ F,
              (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ))) :=
      Finset.sum_congr rfl (fun w _ => by ring)
    rw [hre,Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.mul_sum,hdiag]
    unfold appendixBoxErrCluster
    ring
  -- sum over clusters and insert the explicit inputs
  have hPC (C : Finset (Vertex d)) :
      0 ≤ (percolation d (criticalPoint d)).real {ω | finiteBoxCluster ω Q x = C} :=
    measureReal_nonneg
  have hagg : (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
      (n : ℝ)^((2 : ℝ)-(d : ℝ))*
      ((cb-K₂*(r : ℝ)^((4 : ℝ)-(d : ℝ)))*appendixBoxClusterMean (criticalPoint d) Q x
        (fun C => ((C ∩ F).card : ℝ)) -
      K₁*appendixBoxClusterMean (criticalPoint d) Q x (fun C => appendixBoxErrCluster C F r) -
      K₂*appendixBoxClusterMean (criticalPoint d) Q x (fun C => appendixBoxErrBoundary C F r)) ≤
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
    refine le_trans (le_of_eq ?_) ((Finset.sum_le_sum fun C hC =>
      mul_le_mul_of_nonneg_left (hperC C hC) (hPC C)).trans hstep1)
    simp only [appendixBoxClusterMean,Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C _ => by ring)
  -- final arithmetic
  have hcoef : cb/2 ≤ cb-K₂*(r : ℝ)^((4 : ℝ)-(d : ℝ)) := by linarith
  have hcregn : 0 ≤ creg/(n : ℝ) := div_nonneg hcreg.le hn0.le
  have hpos : cb/2*(creg/(n : ℝ)) ≤ (cb-K₂*(r : ℝ)^((4 : ℝ)-(d : ℝ)))*
      appendixBoxClusterMean (criticalPoint d) Q x (fun C => ((C ∩ F).card : ℝ)) :=
    mul_le_mul hcoef hreg' hcregn (by linarith)
  have hErr1 := mul_le_mul_of_nonneg_left hEcl hK₁
  have hErr2 := mul_le_mul_of_nonneg_left hEbd hK₂
  have hsplitK : ((K₁+K₂)*Kerr)*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ) =
      K₁*(Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ)) +
        K₂*(Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ)) := by ring
  have herrs' : ((K₁+K₂)*Kerr)*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ) ≤ cb*creg/4/(n : ℝ) :=
    div_le_div_of_nonneg_right hKr hn0.le
  have hhalf : cb/2*(creg/(n : ℝ)) = cb*creg/4/(n : ℝ)+cb*creg/4/(n : ℝ) := by ring
  have hbracket : cb*creg/4/(n : ℝ) ≤
      (cb-K₂*(r : ℝ)^((4 : ℝ)-(d : ℝ)))*appendixBoxClusterMean (criticalPoint d) Q x
        (fun C => ((C ∩ F).card : ℝ)) -
      K₁*appendixBoxClusterMean (criticalPoint d) Q x (fun C => appendixBoxErrCluster C F r) -
      K₂*appendixBoxClusterMean (criticalPoint d) Q x (fun C => appendixBoxErrBoundary C F r) := by
    linarith
  have hpow : (n : ℝ)^((2 : ℝ)-(d : ℝ))*(1/(n : ℝ)) = (n : ℝ)^((1 : ℝ)-(d : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one,← Real.rpow_add hn0]
    congr 1
    ring
  have hc₂n : 0 ≤ (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
      (n : ℝ)^((2 : ℝ)-(d : ℝ)) := mul_nonneg hc₂.le hnq
  calc (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*(cb*creg/4)*
        (n : ℝ)^((1 : ℝ)-(d : ℝ))
      = (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))*
          (n : ℝ)^((2 : ℝ)-(d : ℝ))*(cb*creg/4/(n : ℝ)) := by rw [← hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbracket hc₂n
    _ ≤ _ := hagg

/-- Conditional lem.box_twopoint_lower on a negative face, at large scales `α n ≥ 16 r`
for the fixed `r = r(α)`. -/
theorem appendix_box_twopoint_lower_large {d : ℕ} (hd : 7 ≤ d) (asymp : TwoPointAsymptotics d)
    (lower : RestrictedRectangleLowerInput d) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
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
    ∃ c : ℝ, 0 < c ∧ ∃ r : ℕ, 1 ≤ r ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d),
      16*(r : ℝ) ≤ α*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      c*(n : ℝ)^((1 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  refine appendix_box_twopoint_lower_large_on_domain hd asymp lower hα0 le_rfl hα1
    (fun n i x => appendixBoxQ n (Nat.floor (α * (n : ℝ) / 8)) i x)
    (fun n i x => appendixBoxF n (Nat.floor (α * (n : ℝ) / 8)) i x) ?_ hreg ?_
  · intro i n x hn1 hαn16 hxi hx Q F h
    have hhle : (h : ℝ) ≤ α*(n : ℝ)/8 :=
      Nat.floor_le (div_nonneg (mul_nonneg hα0.le (Nat.cast_nonneg n)) (by norm_num))
    have hhge : α*(n : ℝ)/16 ≤ (h : ℝ) := by
      have := Nat.lt_floor_add_one (α*(n : ℝ)/8)
      change α*(n : ℝ)/8 < (h : ℝ)+1 at this
      linarith
    have hxQ : x ∈ Q := by
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
      have hh1 : 1 ≤ h := by
        have : (1 : ℝ) ≤ h := by linarith
        exact_mod_cast this
      refine Finset.mem_filter.mpr ⟨hxbox,?_,?_⟩
      · rw [hxi]
        omega
      · intro j _
        simp only [sub_self,abs_zero]
        omega
    refine ⟨hxQ, appendixBoxQ_subset n h i x, ?_, appendixBoxF_subset n h i x, ?_, ?_⟩
    · intro u hu
      exact (Finset.mem_filter.mp hu).2.1
    · intro w hw
      exact (Finset.mem_filter.mp hw).2
    · intro w hw j hj
      have hwQ := appendixBoxF_subset n h i x hw
      have hdist := (Finset.mem_filter.mp hwQ).2.2 j hj
      have h' : |(w j : ℝ) - (x j : ℝ)| < 2 * (h : ℝ) := by exact_mod_cast hdist
      linarith
  · obtain ⟨K, hK, herr⟩ := herr
    exact ⟨K, hK, fun i n r x hn hr _ hlarge hx hmargin => herr i n r x hn hr hlarge hx hmargin⟩

end NearCritical
