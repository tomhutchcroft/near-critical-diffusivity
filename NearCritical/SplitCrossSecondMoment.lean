module

public import NearCritical.SplitCrossCountIntegrability

/-! A common normalization for all terminal counts gives the second
moment with one inverse box mass from the tree diagram. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

private theorem boxMass_splitEnvelope_le {d t : ℕ} (ht : 1 ≤ t) {G : ℝ} (hG : 0 ≤ G) :
    boxMass d G ((t - 1) / 2 + t) ≤
      (G * (1 + 32 * (d : ℝ) * 3 ^ (d - 1))) * (t : ℝ) ^ 2 := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hside : ((2 * ((t - 1) / 2 + t) : ℕ) : ℝ) + 1 ≤ 4 * (t : ℝ) := by
    exact_mod_cast (show 2 * ((t - 1) / 2 + t) + 1 ≤ 4 * t by omega)
  have hp := pow_le_pow_left₀ (by positivity) hside 2
  unfold boxMass
  have hd : 0 ≤ 2 * (d : ℝ) * 3 ^ (d - 1) := by positivity
  have h1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ G * ((t : ℝ) ^ 2 + (2 * (d : ℝ) * 3 ^ (d - 1)) * (4 * (t : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 (mul_le_mul_of_nonneg_left hp hd)) hG
    _ = _ := by ring

theorem crossing_placement_second_moment {d : ℕ} (hd : 7 ≤ d)
    {G B : ℝ} (hG : 0 < G) (green : CriticalSupGreenUpper d G) (hB : 0 < B)
    (faceMass : Section10.BoxFaceFirstMoment d B) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ≥ 64, ∀ (x : Vertex d), x ∈ centeredBox d ((t - 1) / 32) →
      ∀ axis : Fin d,
      (∫ θ, crossingPlacementCount t x axis θ ^ 2 ∂percolation d (criticalPoint d)) ≤
        C * (t : ℝ) ^ (2 * (40 * d - 1)) := by
  let ι := InteriorIndex d ⊕ Fin (4 * d)
  let n := Fintype.card ι
  let γ := (gammaN (2 * n) (2 * n) : ℝ)
  let G₀ := G * (1 + 32 * (d : ℝ) * 3 ^ (d - 1))
  have hn : 0 < n := by
    dsimp [n, ι, InteriorIndex]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  have hG₀ : 0 < G₀ := by dsimp [G₀]; positivity
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  let C := (γ + 1) * B ^ (8 * d) * G₀ ^ (40 * d - 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht x hx axis
  let N := (t - 1) / 2 + t
  let D := (centeredBox d N : Set (Vertex d))
  let p := criticalPoint d
  let μ := percolation d p
  let m := boxMass d G N
  have hm : 0 < m := by dsimp [m, boxMass]; positivity
  have hxD : x ∈ centeredBox d N :=
    nodeSites_subset_envelope ht hx axis root (by simp [nodeSites])
  let Y : ι → Finset (Vertex d)
    | .inl i => nodeSites t x axis (interiorNode i)
    | .inr k => nodeSites t x axis (face k)
  let S : ι → ℝ
    | .inl _ => m ^ 4
    | .inr _ => (B * m) ^ 2
  have hS (i : ι) : 0 < S i := by cases i <;> dsimp [S] <;> positivity
  let e := Fintype.equivFin ι
  let X (j : Fin n) (θ : Configuration d) := countIn D (Y (e.symm j)) x θ ^ 2
  let s (j : Fin n) := S (e.symm j)
  have hs (j : Fin n) : 0 < s j := hS (e.symm j)
  have hX (j : Fin n) (θ : Configuration d) : 0 ≤ X j θ := sq_nonneg _
  have hprod : Integrable (fun θ => ∏ j, X j θ) μ := by
    refine Integrable.of_bound (Finset.measurable_fun_prod _ (fun j _ =>
      (countIn_measurable D (Y (e.symm j)) x).pow_const 2)).aestronglyMeasurable
      (∏ j : Fin n, ((Y (e.symm j)).card : ℝ) ^ 2) (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun j _ => hX j θ)]
    exact Finset.prod_le_prod₀ (fun j _ => hX j θ) fun j _ =>
      pow_le_pow_left₀ (countIn_nonneg D _ x θ) (countIn_le_card D _ x θ) _
  have hnormalize (j : Fin n) (θ : Configuration d) :
      (X j θ / s j) ^ n = countIn D (Y (e.symm j)) x θ ^ (2 * n) * (s j ^ n)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
    dsimp only [X]
    rw [← pow_mul]
  have hpow (j : Fin n) : Integrable (fun θ => (X j θ / s j) ^ n) μ := by
    simp_rw [hnormalize j]
    exact (countIn_pow_integrable D (Y (e.symm j)) x p (2 * n)).mul_const _
  have hraw (i : ι) : (∫ θ, countIn D (Y i) x θ ^ (2 * n) ∂μ) ≤ γ * (S i ^ n / m) := by
    have h2n : 0 < 2 * n := by omega
    have hm_pow : m ^ (2 * n) / m = m ^ (2 * n - 1) := by
      rw [← Nat.sub_add_cancel (show 1 ≤ 2 * n by omega), pow_succ, mul_div_cancel_right₀ _ hm.ne', Nat.add_sub_cancel]
    cases i with
    | inl i =>
      have hY : Y (.inl i) ⊆ centeredBox d N :=
        nodeSites_subset_envelope ht hx axis (interiorNode i)
      have hYne : 0 < (Y (.inl i)).card :=
        Finset.card_pos.mpr (nodeSites_nonempty t x axis (interiorNode i))
      have h := box_interior_count_moment_le (by omega : 2 ≤ d) hG.le green N (2 * n) h2n hY hYne hxD
      refine h.trans_eq ?_
      change γ * m ^ (2 * n) * m ^ (2 * n - 1) = γ * ((m ^ 4) ^ n / m)
      have h₄ : m ^ (2 * n) * m ^ (2 * n) = (m ^ 4) ^ n := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      rw [← hm_pow, ← h₄]
      ring
    | inr k =>
      let f := (splitLegEquiv d k).1
      let F := signedCubeFace d N f
      have hY : Y (.inr k) ⊆ F := farLegFaceCore_subset_envelope_face ht f (splitLegEquiv d k).2
      have hF : 0 < F.card := Finset.card_pos.mpr
        ((nodeSites_nonempty t x axis (face k)).mono hY)
      have h := box_face_count_moment_le (by omega : 2 ≤ d) hG.le hB.le green faceMass N (2 * n) h2n f hF hxD
      refine (integral_mono (countIn_pow_integrable D _ x p _) (countIn_pow_integrable D F x p _)
        (fun θ => pow_le_pow_left₀ (countIn_nonneg D _ x θ) (countIn_mono D hY x θ) _)).trans
        (h.trans_eq ?_)
      change γ * B ^ (2 * n) * m ^ (2 * n - 1) = γ * (((B * m) ^ 2) ^ n / m)
      rw [← hm_pow, ← pow_mul, mul_pow]
      ring
  have hnorm (j : Fin n) : (∫ θ, (X j θ / s j) ^ n ∂μ) ≤ γ / m := by
    simp_rw [hnormalize j]
    rw [integral_mul_const]
    have hinv : 0 ≤ (s j ^ n)⁻¹ := inv_nonneg.mpr (pow_nonneg (hs j).le _)
    refine (mul_le_mul_of_nonneg_right (hraw (e.symm j)) hinv).trans_eq ?_
    change (γ * (s j ^ n / m)) * (s j ^ n)⁻¹ = γ / m
    field_simp [(pow_pos (hs j) n).ne', hm.ne']
  have hmean := integral_prod_le_scaled μ hn X s hs hX hprod hpow
  have havg : (n : ℝ)⁻¹ * ∑ j, ∫ θ, (X j θ / s j) ^ n ∂μ ≤ γ / m := by
    calc
      _ ≤ (n : ℝ)⁻¹ * ∑ _j : Fin n, γ / m :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hnorm j) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        field_simp
  have hpt (θ : Configuration d) : crossingPlacementCount t x axis θ ^ 2 ≤ ∏ j, X j θ := by
    have hprod_eq : (∏ j, X j θ) =
        ((∏ i : InteriorIndex d, countIn D (Y (.inl i)) x θ) *
          (∏ k : Fin (4 * d), countIn D (Y (.inr k)) x θ)) ^ 2 := by
      rw [Fintype.prod_equiv e.symm (fun j => X j θ) (fun i : ι => countIn D (Y i) x θ ^ 2) (fun _ => rfl)]
      rw [Fintype.prod_sum_type, mul_pow, Finset.prod_pow, Finset.prod_pow]
    rw [hprod_eq]
    by_cases hθ : θ ∈ Section10.crossAll t t x
    · unfold crossingPlacementCount
      rw [Set.indicator_of_mem hθ]
      exact le_rfl
    · unfold crossingPlacementCount
      rw [Set.indicator_of_notMem hθ, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hscale : (∏ j, s j) = B ^ (8 * d) * m ^ (40 * d) := by
    rw [Fintype.prod_equiv e.symm s S (fun _ => rfl), Fintype.prod_sum_type]
    simp only [S, Finset.prod_const, Finset.card_univ, InteriorIndex, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, ← pow_mul]
    rw [mul_pow]
    have h₁ : 2 * (4 * d) = 8 * d := by omega
    have h₂ : 4 * (4 * d * 2) + 8 * d = 40 * d := by omega
    rw [h₁, mul_left_comm, ← pow_add, h₂]
  have hm_pow : m ^ (40 * d) / m = m ^ (40 * d - 1) := by
    rw [show 40 * d = (40 * d - 1) + 1 by omega, pow_succ, mul_div_cancel_right₀ _ hm.ne', Nat.add_sub_cancel]
  calc
    _ ≤ ∫ θ, ∏ j, X j θ ∂μ :=
      integral_mono (crossingPlacementCount_integrable t x axis p 2) hprod hpt
    _ ≤ (∏ j, s j) * (γ / m) :=
      hmean.trans (mul_le_mul_of_nonneg_left havg (Finset.prod_nonneg fun j _ => (hs j).le))
    _ = γ * B ^ (8 * d) * m ^ (40 * d - 1) := by
      rw [hscale, ← hm_pow]
      ring
    _ ≤ (γ + 1) * B ^ (8 * d) * (G₀ * (t : ℝ) ^ 2) ^ (40 * d - 1) := by
      have hM : m ≤ G₀ * (t : ℝ) ^ 2 :=
        boxMass_splitEnvelope_le (d := d) (show 1 ≤ t by omega) hG.le
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith : γ ≤ γ + 1) (by positivity))
        (pow_le_pow_left₀ hm.le hM _) (by positivity) (by positivity)
    _ = C * (t : ℝ) ^ (2 * (40 * d - 1)) := by
      dsimp only [C]
      rw [mul_pow, pow_mul (t : ℝ) 2 (40 * d - 1), ← mul_assoc]

end NearCritical.SplitCrossDirect
