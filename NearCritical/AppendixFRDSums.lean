module

public import NearCritical.AppendixRDGeometry


/-! Analytic core of source lem.F_RD (Appendix B): the two `y`-sums in its proof are `≲ n³`.

(S1) `frd_bulk_sum_le`: `∑_{y ∈ S} w_y / max(r, |x-y|+1)^{d-2} ≤ 2d·3^{d-1}(2n+1)³` for
`S ⊆ Λ_n`, `x ∈ Λ_n` and weights `0 ≤ w_y ≤ |x-y|+1`. The source sums over
`Λ_n \ Λ_{3n/4}` with `w_y = 1 + l_y` and `l_y ≤ |x-y|`.

(S2) `boundary_maxr_pow_sum_le`: `∑_{y ∈ ∂Λ_n} 1/max(r, |x-y|+1)^{d-4} ≤ 4k(k+1)·3^{k-1}(2n+1)³`
(`d = k+1 ≥ 4`), proved face by face: for each `j` and sign, project to the other `k`
coordinates, then apply a `k`-dimensional radial sum. NOTE: the source's per-shell claim
`#{y ∈ ∂Λ_n : |x-y| = m} ≲ m^{d-2}` fails at `m` equal to the distance to the opposite face
(`~m^{d-1}` there). The total `≲ n³` is still true, and this proof avoids the per-shell claim.

The probabilistic lem.RD_bound input of lem.F_RD is not addressed here. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `Λ_n ⊆ ball(x, 2n)` for `x ∈ Λ_n`. -/
theorem cube_subset_linfBall_two {D n : ℕ} {x : Fin D → ℤ}
    (hx : x ∈ (cube n : Finset (Fin D → ℤ))) :
    (cube n : Finset (Fin D → ℤ)) ⊆ linfBall x ((2 * n : ℕ) : ℤ) := by
  intro u hu
  rw [mem_cube] at hu hx
  rw [mem_linfBall]
  intro i
  have h1 := hu i
  have h2 := hx i
  rw [abs_le] at h1 h2 ⊢
  push_cast
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- (S1, ball form) `∑_{y∈ball(x,K)} (|x-y|+1)/max(r,|x-y|+1)^{d-2} ≤ 2d·3^{d-1}(K+1)³`. -/
theorem frd_bulk_ball_sum {d : ℕ} (hd : 2 ≤ d) (x : Fin d → ℤ) (r K : ℕ) :
    ∑ y ∈ linfBall x (K : ℤ), ((linfDist x y + 1 : ℕ) : ℝ) /
        (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 3 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  refine (radial_sum_shell_bound (by omega) x K
    (fun j => ((j + 1 : ℕ) : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 2 - 2))
    (fun j => by positivity)).trans ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * ((e + 2 : ℕ) : ℝ) * 3 ^ (e + 2 - 1) * ((j + 1 : ℕ) : ℝ) ^ (e + 2 - 1) *
        (((j + 1 : ℕ) : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 2 - 2))
      ≤ 2 * ((e + 2 : ℕ) : ℝ) * 3 ^ (e + 2 - 1) * ((K : ℝ) + 1) ^ 2 := by
    intro j hj
    have hjK : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) + 1 := by
      have := Finset.mem_range.mp hj
      exact_mod_cast (show j + 1 ≤ K + 1 by omega)
    have ht1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + 1 by omega)
    have htpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by linarith
    have hmax : ((j + 1 : ℕ) : ℝ) ≤ max (r : ℝ) ((j + 1 : ℕ) : ℝ) := le_max_right _ _
    have hm : (0 : ℝ) < (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e := by positivity
    rw [show e + 2 - 2 = e by omega, show e + 2 - 1 = e + 1 by omega]
    have hkey : ((j + 1 : ℕ) : ℝ) ^ (e + 1) *
        (((j + 1 : ℕ) : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e) ≤
        ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hm]
      calc ((j + 1 : ℕ) : ℝ) ^ (e + 1) * ((j + 1 : ℕ) : ℝ)
          = ((j + 1 : ℕ) : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ e := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le hmax e) (by positivity)
    have ht2 : ((j + 1 : ℕ) : ℝ) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := pow_le_pow_left₀ htpos.le hjK 2
    calc _ = 2 * ((e + 2 : ℕ) : ℝ) * 3 ^ (e + 1) * (((j + 1 : ℕ) : ℝ) ^ (e + 1) *
            (((j + 1 : ℕ) : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hkey.trans ht2) (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- (S1) The lem.F_RD bulk sum: for `S ⊆ Λ_n`, `x ∈ Λ_n` and weights `0 ≤ w_y ≤ |x-y|+1`,
`∑_{y∈S} w_y/max(r,|x-y|+1)^{d-2} ≤ 2d·3^{d-1}(2n+1)³`. -/
theorem frd_bulk_sum_le {d : ℕ} (hd : 2 ≤ d) {n r : ℕ} {x : Fin d → ℤ}
    (hx : x ∈ (cube n : Finset (Fin d → ℤ))) (S : Finset (Fin d → ℤ))
    (hS : S ⊆ (cube n : Finset (Fin d → ℤ))) (wt : (Fin d → ℤ) → ℝ)
    (hw0 : ∀ y ∈ S, 0 ≤ wt y) (hw : ∀ y ∈ S, wt y ≤ ((linfDist x y + 1 : ℕ) : ℝ)) :
    ∑ y ∈ S, wt y / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (2 * (n : ℝ) + 1) ^ 3 := by
  calc _ ≤ ∑ y ∈ S, ((linfDist x y + 1 : ℕ) : ℝ) /
          (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2) :=
        Finset.sum_le_sum (fun y hy => div_le_div_of_nonneg_right (hw y hy) (by positivity))
    _ ≤ ∑ y ∈ linfBall x ((2 * n : ℕ) : ℤ), ((linfDist x y + 1 : ℕ) : ℝ) /
          (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (hS.trans (cube_subset_linfBall_two hx))
          (fun _ _ _ => by positivity)
    _ ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((2 * n : ℕ) : ℝ) + 1) ^ 3 := frd_bulk_ball_sum hd x r _
    _ = _ := by push_cast; ring

/-- `k`-dimensional cubic radial sum: `∑_{y∈ball(x,K)} 1/max(r,|x-y|+1)^{k-3} ≤ 2k·3^{k-1}(K+1)³`. -/
theorem ball_maxr_pow_cubic {k : ℕ} (hk : 3 ≤ k) (x : Fin k → ℤ) (r K : ℕ) :
    ∑ y ∈ linfBall x (K : ℤ), (1 : ℝ) / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (k - 3)
      ≤ 2 * (k : ℝ) * 3 ^ (k - 1) * ((K : ℝ) + 1) ^ 3 := by
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 3 := ⟨k - 3, by omega⟩
  refine (radial_sum_shell_bound (by omega) x K
    (fun j => (1 : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 3 - 3))
    (fun j => by positivity)).trans ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * ((e + 3 : ℕ) : ℝ) * 3 ^ (e + 3 - 1) * ((j + 1 : ℕ) : ℝ) ^ (e + 3 - 1) *
        ((1 : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 3 - 3))
      ≤ 2 * ((e + 3 : ℕ) : ℝ) * 3 ^ (e + 3 - 1) * ((K : ℝ) + 1) ^ 2 := by
    intro j hj
    have hjK : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) + 1 := by
      have := Finset.mem_range.mp hj
      exact_mod_cast (show j + 1 ≤ K + 1 by omega)
    have ht1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + 1 by omega)
    have htpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by linarith
    have hmax : ((j + 1 : ℕ) : ℝ) ≤ max (r : ℝ) ((j + 1 : ℕ) : ℝ) := le_max_right _ _
    have hm : (0 : ℝ) < (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e := by positivity
    rw [show e + 3 - 3 = e by omega, show e + 3 - 1 = e + 2 by omega]
    have hkey : ((j + 1 : ℕ) : ℝ) ^ (e + 2) *
        ((1 : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [mul_one_div, div_le_iff₀ hm]
      calc ((j + 1 : ℕ) : ℝ) ^ (e + 2)
          = ((j + 1 : ℕ) : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ e := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le hmax e) (by positivity)
    have ht2 : ((j + 1 : ℕ) : ℝ) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := pow_le_pow_left₀ htpos.le hjK 2
    calc _ = 2 * ((e + 3 : ℕ) : ℝ) * 3 ^ (e + 2) * (((j + 1 : ℕ) : ℝ) ^ (e + 2) *
            ((1 : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ e)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hkey.trans ht2) (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The cube boundary `∂Λ_n = {y ∈ Λ_n : |y|_∞ = n}`. -/
def cubeBoundary {D : ℕ} (n : ℕ) : Finset (Fin D → ℤ) :=
  (cube n : Finset (Fin D → ℤ)).filter (fun y => linfDist (0 : Fin D → ℤ) y = n)

/-- The `r`-floored kernel `1/max(r, |x-y|+1)^e`. -/
noncomputable def frdKernel {D : ℕ} (r e : ℕ) (x y : Fin D → ℤ) : ℝ :=
  1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ e

/-- Dropping coordinate `j` does not increase the ℓ∞ distance. -/
theorem linfDist_removeNth_le {k : ℕ} (x : Fin (k + 1) → ℤ) (j : Fin (k + 1)) (σ : ℤ)
    (u : Fin k → ℤ) :
    linfDist (Fin.removeNth j x) u ≤
      linfDist x (Fin.insertNth (α := fun _ => ℤ) j σ u) := by
  unfold linfDist
  apply Finset.sup_le
  intro i _
  have h := Finset.le_sup
    (f := fun i => (x i - Fin.insertNth (α := fun _ => ℤ) j σ u i).natAbs)
    (Finset.mem_univ (j.succAbove i))
  simpa [Fin.removeNth, Fin.insertNth_apply_succAbove] using h

/-- (S2) The lem.F_RD boundary sum, `d = k+1 ≥ 4`:
`∑_{y∈∂Λ_n} 1/max(r,|x-y|+1)^{d-4} ≤ (k+1)·2·2k·3^{k-1}(2n+1)³` for `x ∈ Λ_n`. -/
theorem boundary_maxr_pow_sum_le {k : ℕ} (hk : 3 ≤ k) {n r : ℕ} {x : Fin (k + 1) → ℤ}
    (hx : x ∈ (cube n : Finset (Fin (k + 1) → ℤ))) :
    ∑ y ∈ (cubeBoundary n : Finset (Fin (k + 1) → ℤ)),
        (1 : ℝ) / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (k - 3)
      ≤ ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1) * (2 * (n : ℝ) + 1) ^ 3)) := by
  change ∑ y ∈ (cubeBoundary n : Finset (Fin (k + 1) → ℤ)), frdKernel r (k - 3) x y ≤ _
  set C : ℝ := 2 * (k : ℝ) * 3 ^ (k - 1) * (2 * (n : ℝ) + 1) ^ 3 with hC
  have hC0 : 0 ≤ C := by positivity
  have hnonneg : ∀ y : Fin (k + 1) → ℤ, 0 ≤ frdKernel r (k - 3) x y := fun y => by
    unfold frdKernel; positivity
  set P := (Finset.univ : Finset (Fin (k + 1))) ×ˢ ({(n : ℤ), -(n : ℤ)} : Finset ℤ) ×ˢ
    (cube n : Finset (Fin k → ℤ)) with hP
  have hsub : (cubeBoundary n : Finset (Fin (k + 1) → ℤ)) ⊆
      P.image (fun p => (Fin.insertNth (α := fun _ => ℤ) p.1 p.2.1 p.2.2 :
        Fin (k + 1) → ℤ)) := by
    intro y hy
    unfold cubeBoundary at hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hcube, hn⟩ := hy
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k + 1)))
      Finset.univ_nonempty (fun i => (y i).natAbs)
    have hyj : (y j).natAbs = n := by rw [← hn, linfDist_zero, hj]
    rw [Finset.mem_image]
    refine ⟨(j, y j, Fin.removeNth j y), ?_, Fin.insertNth_self_removeNth j y⟩
    rw [hP]
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨by omega, ?_⟩
    rw [mem_cube] at hcube ⊢
    intro i
    simpa [Fin.removeNth] using hcube (j.succAbove i)
  have hinner : ∀ (j : Fin (k + 1)) (σ : ℤ),
      ∑ u ∈ (cube n : Finset (Fin k → ℤ)),
          frdKernel r (k - 3) x (Fin.insertNth (α := fun _ => ℤ) j σ u) ≤ C := by
    intro j σ
    have hxj : Fin.removeNth j x ∈ (cube n : Finset (Fin k → ℤ)) := by
      rw [mem_cube] at hx ⊢
      intro i
      simpa [Fin.removeNth] using hx (j.succAbove i)
    calc _ ≤ ∑ u ∈ (cube n : Finset (Fin k → ℤ)), frdKernel r (k - 3) (Fin.removeNth j x) u := by
          apply Finset.sum_le_sum
          intro u _
          unfold frdKernel
          apply one_div_le_one_div_of_le (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          apply max_le_max le_rfl
          exact_mod_cast Nat.add_le_add_right (linfDist_removeNth_le x j σ u) 1
      _ ≤ ∑ u ∈ linfBall (Fin.removeNth j x) ((2 * n : ℕ) : ℤ),
            frdKernel r (k - 3) (Fin.removeNth j x) u :=
          Finset.sum_le_sum_of_subset_of_nonneg (cube_subset_linfBall_two hxj)
            (fun _ _ _ => by unfold frdKernel; positivity)
      _ ≤ 2 * (k : ℝ) * 3 ^ (k - 1) * (((2 * n : ℕ) : ℝ) + 1) ^ 3 :=
          ball_maxr_pow_cubic hk (Fin.removeNth j x) r (2 * n)
      _ = C := by rw [hC]; push_cast; ring
  have hScard : (({(n : ℤ), -(n : ℤ)} : Finset ℤ)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  calc _ ≤ ∑ y ∈ P.image (fun p => (Fin.insertNth (α := fun _ => ℤ) p.1 p.2.1 p.2.2 :
          Fin (k + 1) → ℤ)), frdKernel r (k - 3) x y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hnonneg y)
    _ ≤ ∑ p ∈ P, frdKernel r (k - 3) x
          (Fin.insertNth (α := fun _ => ℤ) p.1 p.2.1 p.2.2) :=
        Finset.sum_image_le_of_nonneg (fun y _ => hnonneg y)
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))), ∑ σ ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ),
          ∑ u ∈ (cube n : Finset (Fin k → ℤ)),
            frdKernel r (k - 3) x (Fin.insertNth (α := fun _ => ℤ) j σ u) := by
        rw [hP, Finset.sum_product]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_product]
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))),
          ∑ σ ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ), C :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun σ _ => hinner j σ))
    _ = ((k : ℝ) + 1) * (((({(n : ℤ), -(n : ℤ)} : Finset ℤ)).card : ℝ) * C) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring
    _ ≤ ((k : ℝ) + 1) * (2 * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) hC0)
          (by positivity)

end NearCritical.AppendixVariance
