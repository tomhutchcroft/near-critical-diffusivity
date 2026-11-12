module

public import NearCritical.AppendixFRDSums
public import NearCritical.Bernoulli

/-! The depth-weighted two-center lattice convolution in Ef2. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance
open scoped Classical

private lemma branch_kernel_le_nearer {d : ℕ} (hd : 3 ≤ d)
    {a b s depth : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : s ≤ a + b)
    (hdepth : 0 ≤ depth) (hda : depth ≤ a) :
    depth ^ 3 / (a ^ d * b ^ d) ≤ (2 : ℝ) ^ d / (a ^ (d - 3) * (max s a) ^ d) := by
  have hb : 0 < b := ha.trans_le hab
  have hm : 0 < max s a := ha.trans_le (le_max_right _ _)
  have hmax : max s a ≤ 2 * b := max_le (by linarith) (by linarith)
  have hpow : (max s a) ^ d ≤ (2 : ℝ) ^ d * b ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hm.le hmax d
  have hprod : depth ^ 3 * (max s a) ^ d ≤ a ^ 3 * ((2 : ℝ) ^ d * b ^ d) :=
    mul_le_mul (pow_le_pow_left₀ hdepth hda 3) hpow (by positivity) (by positivity)
  have hsplit : a ^ 3 * a ^ (d - 3) = a ^ d := by
    rw [← pow_add, show 3 + (d - 3) = d by omega]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ = (depth ^ 3 * (max s a) ^ d) * a ^ (d - 3) := by ring
    _ ≤ (a ^ 3 * ((2 : ℝ) ^ d * b ^ d)) * a ^ (d - 3) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = _ := by
      calc
        _ = (2 : ℝ) ^ d * ((a ^ 3 * a ^ (d - 3)) * b ^ d) := by ring
        _ = _ := by rw [hsplit]

/-- The two-sided boundary legs, with the three depth factors supplied by
the legs and the heart profile, have convolution order `(1 + |x-y|)^(3-d)`.
The clipped distances cover both diagonal and off-diagonal terms. -/
theorem boundary_branch_convolution_le {d : ℕ} (hd : 4 ≤ d) (x y : Vertex d)
    (U : Finset (Vertex d)) (depth : Vertex d → ℝ)
    (hdepth : ∀ u ∈ U, 0 ≤ depth u)
    (hx : ∀ u ∈ U, depth u ≤ ((linfDist x u + 1 : ℕ) : ℝ))
    (hy : ∀ u ∈ U, depth u ≤ ((linfDist y u + 1 : ℕ) : ℝ)) :
    ∑ u ∈ U, depth u ^ 3 /
        (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist y u + 1 : ℕ) : ℝ) ^ d) ≤
      ((2 : ℝ) ^ d * (2 * (2 * (d : ℝ) * 3 ^ (d - 1))) *
        ((((d - 3 : ℕ) : ℝ) + 1) / ((d - 3 : ℕ) : ℝ))) /
        ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 3) := by
  let r := linfDist x y + 1
  let shell (v u : Vertex d) : ℝ := (linfDist v u + 1 : ℕ)
  let K (v u : Vertex d) := (1 : ℝ) / (shell v u ^ (d - 3) * (max (r : ℝ) (shell v u)) ^ d)
  let C : ℝ := 2 * (d : ℝ) * 3 ^ (d - 1)
  let B : ℝ := C * ((((d - 3 : ℕ) : ℝ) + 1) / (((d - 3 : ℕ) : ℝ) * (r : ℝ) ^ (d - 3)))
  have hK (v u : Vertex d) : 0 ≤ K v u := by dsimp [K, shell]; positivity
  have hsum (v : Vertex d) : ∑ u ∈ U, K v u ≤ B := by
    let R := U.sup (linfDist v)
    have hsub : U ⊆ linfBall v (R : ℤ) := by
      intro u hu
      apply (mem_linfBall_iff_dist _ _ (Int.natCast_nonneg R)).mpr
      simpa only [Int.toNat_natCast] using (Finset.le_sup (f := linfDist v) hu)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hK v u)).trans ?_
    simpa only [K, shell, B, C, show (d - 1 - (d - 3)) + ((d - 3) + 1) = d by omega] using
      (radial_div_sum_le (by omega : 1 ≤ d) v (d - 3) (by omega)
        (t := d - 3) (r := r) (by omega) (by dsimp [r]; omega) R)
  have hterm (u : Vertex d) (hu : u ∈ U) :
      depth u ^ 3 / (shell x u ^ d * shell y u ^ d) ≤ (2 : ℝ) ^ d * (K x u + K y u) := by
    have htri := linfDist_triangle x u y
    rw [linfDist_comm u y] at htri
    have htri' : r ≤ (linfDist x u + 1) + (linfDist y u + 1) := by dsimp [r]; omega
    have hs : (r : ℝ) ≤ shell x u + shell y u := by dsimp [shell]; exact_mod_cast htri'
    have hpx : 0 < shell x u := by dsimp [shell]; positivity
    have hpy : 0 < shell y u := by dsimp [shell]; positivity
    rcases le_total (shell x u) (shell y u) with hxy | hyx
    · have h := branch_kernel_le_nearer (by omega : 3 ≤ d) hpx hxy hs (hdepth u hu) (hx u hu)
      have h' : depth u ^ 3 / (shell x u ^ d * shell y u ^ d) ≤ (2 : ℝ) ^ d * K x u := by
        simpa only [K, ← mul_div_assoc, mul_one] using h
      exact h'.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hK y u)) (by positivity))
    · have h := branch_kernel_le_nearer (by omega : 3 ≤ d) hpy hyx
        (by simpa only [add_comm] using hs) (hdepth u hu) (hy u hu)
      have h' : depth u ^ 3 / (shell x u ^ d * shell y u ^ d) ≤ (2 : ℝ) ^ d * K y u := by
        simpa only [mul_comm (shell y u ^ d) (shell x u ^ d), K, ← mul_div_assoc, mul_one] using h
      exact h'.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hK x u)) (by positivity))
  change (∑ u ∈ U, depth u ^ 3 / (shell x u ^ d * shell y u ^ d)) ≤ _
  calc
    _ ≤ ∑ u ∈ U, (2 : ℝ) ^ d * (K x u + K y u) := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ d * ((∑ u ∈ U, K x u) + ∑ u ∈ U, K y u) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ d * (B + B) := mul_le_mul_of_nonneg_left (add_le_add (hsum x) (hsum y)) (by positivity)
    _ = _ := by
      dsimp [B, C, r]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The remaining radial sum on the entire cube boundary. Projecting each
face onto its free coordinates gives the source power `r^(6-d)`. -/
theorem boundary_branch_radial_sum_le {k n r : ℕ} (hk : 6 ≤ k) (hr : 1 ≤ r)
    (x : Vertex (k + 1)) (hx : x ∈ (cube n : Finset (Vertex (k + 1)))) :
    ∑ y ∈ (cubeBoundary n : Finset (Vertex (k + 1))),
        (1 : ℝ) / (((linfDist x y + 1 : ℕ) : ℝ) ^ (k - 2) *
          (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (k - 3)) ≤
      ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1) *
        ((((k - 5 : ℕ) : ℝ) + 1) / (((k - 5 : ℕ) : ℝ) * (r : ℝ) ^ (k - 5))))) := by
  let f (m : ℕ) : ℝ := 1 / (((m + 1 : ℕ) : ℝ) ^ (k - 2) *
    (max (r : ℝ) ((m + 1 : ℕ) : ℝ)) ^ (k - 3))
  let C : ℝ := 2 * (k : ℝ) * 3 ^ (k - 1) *
    ((((k - 5 : ℕ) : ℝ) + 1) / (((k - 5 : ℕ) : ℝ) * (r : ℝ) ^ (k - 5)))
  let signs : Finset ℤ := {(n : ℤ), -(n : ℤ)}
  let P := (Finset.univ : Finset (Fin (k + 1))) ×ˢ signs ×ˢ (cube n : Finset (Vertex k))
  let lift (p : Fin (k + 1) × ℤ × Vertex k) : Vertex (k + 1) :=
    Fin.insertNth (α := fun _ => ℤ) p.1 p.2.1 p.2.2
  have hf (m : ℕ) : 0 ≤ f m := by dsimp [f]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmono : Antitone f := by
    intro a b hab
    have h : ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hab
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h _)
      (pow_le_pow_left₀ (by positivity) (max_le_max le_rfl h) _) (by positivity) (by positivity)
  have hcover : (cubeBoundary n : Finset (Vertex (k + 1))) ⊆ P.image lift := by
    intro y hy
    obtain ⟨hyQ, hyn⟩ := Finset.mem_filter.mp hy
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k + 1)))
      Finset.univ_nonempty (fun i => (y i).natAbs)
    have hyj : (y j).natAbs = n := by rw [← hyn, linfDist_zero, hj]
    apply Finset.mem_image.mpr
    refine ⟨(j, y j, Fin.removeNth j y), ?_, Fin.insertNth_self_removeNth j y⟩
    simp only [P, signs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨by omega, ?_⟩
    rw [mem_cube] at hyQ ⊢
    intro i
    simpa [Fin.removeNth] using hyQ (j.succAbove i)
  have hface (j : Fin (k + 1)) (σ : ℤ) :
      ∑ u ∈ (cube n : Finset (Vertex k)), f (linfDist x (lift (j, σ, u))) ≤ C := by
    let z := Fin.removeNth j x
    have hz : z ∈ (cube n : Finset (Vertex k)) := by
      rw [mem_cube] at hx ⊢
      intro i
      simpa [z, Fin.removeNth] using hx (j.succAbove i)
    have hproj (u : Vertex k) : linfDist z u ≤ linfDist x (lift (j, σ, u)) := by
      unfold linfDist
      apply Finset.sup_le
      intro i _
      have h := Finset.le_sup (f := fun i => (x i - lift (j, σ, u) i).natAbs)
        (Finset.mem_univ (j.succAbove i))
      simpa [z, lift, Fin.removeNth, Fin.insertNth_apply_succAbove] using h
    calc
      _ ≤ ∑ u ∈ (cube n : Finset (Vertex k)), f (linfDist z u) :=
        Finset.sum_le_sum fun u _ => hmono (hproj u)
      _ ≤ ∑ u ∈ linfBall z ((2 * n : ℕ) : ℤ), f (linfDist z u) :=
        Finset.sum_le_sum_of_subset_of_nonneg (cube_subset_linfBall_two hz) (fun u _ _ => hf _)
      _ ≤ _ := by
        simpa only [f, C, show (k - 1 - (k - 2)) + ((k - 5) + 1) = k - 3 by omega] using
          (radial_div_sum_le (by omega : 1 ≤ k) z (k - 2) (by omega) (t := k - 5) (by omega) hr (2 * n))
  have hsigns : signs.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  change (∑ y ∈ (cubeBoundary n : Finset (Vertex (k + 1))), f (linfDist x y)) ≤ _
  calc
    _ ≤ ∑ y ∈ P.image lift, f (linfDist x y) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun y _ _ => hf _)
    _ ≤ ∑ p ∈ P, f (linfDist x (lift p)) := Finset.sum_image_le_of_nonneg (fun y _ => hf _)
    _ = ∑ j : Fin (k + 1), ∑ σ ∈ signs, ∑ u ∈ (cube n : Finset (Vertex k)),
        f (linfDist x (lift (j, σ, u))) := by
      dsimp only [P]
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.sum_product]
    _ ≤ ∑ _j : Fin (k + 1), ∑ _σ ∈ signs, C :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun σ _ => hface j σ
    _ = ((k : ℝ) + 1) * ((signs.card : ℝ) * C) := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, nsmul_eq_mul]
      push_cast <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hsigns) hC) (by positivity)

end NearCritical.Section8
