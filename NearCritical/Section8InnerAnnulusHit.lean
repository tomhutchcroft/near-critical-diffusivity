module

public import NearCritical.AppendixErrBoundary
public import NearCritical.Section8FiveDiagrams
public import NearCritical.Section8SourceAnnulusBridge
public import NearCritical.WaterCubeOrdinaryArms

/-! Ordinary-arm control of the inner branch-point mass in Ef1 and Ef2. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

private lemma linfDist_le_dist {d : ℕ} (u v : Vertex d) : (linfDist u v : ℝ) ≤ dist u v := by
  unfold linfDist
  apply Finset.sup_induction (p := fun m : ℕ => (m : ℝ) ≤ dist u v)
  · simpa using (dist_nonneg : 0 ≤ dist u v)
  · intro a ha b hb
    change ((max a b : ℕ) : ℝ) ≤ dist u v
    simpa only [Nat.cast_max] using max_le ha hb
  · intro i _
    simpa only [Int.dist_eq, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub] using
      dist_le_pi_dist u v i

/-- A connection to the heart boundary must realize an ordinary arm of at
least the radial gap. The clipped bound also includes the zero-gap shell. -/
theorem annulusG_le_ordinary_arm {k N H : ℕ} (C : ℝ) (hC : 1 ≤ C)
    (ordinary : OrdinaryArmWindowInput (k + 1) C) (u : Vertex (k + 1)) :
    annulusG (criticalPoint (k + 1)) (centeredBox (k + 1) N) (centeredBox (k + 1) H) u ≤
      4 * C / ((linfDist 0 u - H + 1 : ℕ) : ℝ) ^ 2 := by
  let m := linfDist 0 u - H
  change (percolation (k + 1) (criticalPoint (k + 1))).real
    (annulusHit (centeredBox (k + 1) N) (centeredBox (k + 1) H) u) ≤
      4 * C / ((m + 1 : ℕ) : ℝ) ^ 2
  by_cases hm : m = 0
  · rw [hm]
    norm_num only [zero_add, Nat.cast_one, one_pow, div_one]
    exact measureReal_le_one.trans (by linarith)
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hsub : annulusHit (centeredBox (k + 1) N) (centeredBox (k + 1) H) u ⊆
      extrinsicRadiusArmEvent u ((m : ℝ) / 2) := by
    rintro ω ⟨_, v, hv, _, hpath⟩
    have hvH := (centeredBox_boundary_norm_iff v).mp hv
    have htri := linfDist_triangle 0 v u
    rw [hvH, linfDist_comm v u] at htri
    have hmuv : m ≤ linfDist u v := by dsimp [m]; omega
    have hmuv' : (m : ℝ) ≤ linfDist u v := by exact_mod_cast hmuv
    have hgraph : restrictedGraph ω
        (heartAnnulus (centeredBox (k + 1) N) (centeredBox (k + 1) H) : Set (Vertex (k + 1))) ≤
        openGraph ω := fun _ _ h => h.1
    refine ⟨v, ?_, hpath.mono hgraph⟩
    linarith [linfDist_le_dist u v]
  have hprob := ordinary (criticalPoint (k + 1)) u m hm1
    (le_add_of_nonneg_right (by positivity))
  refine (measureReal_mono hsub).trans (hprob.trans ?_)
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hsq : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ (m : ℝ) + 1 by positivity)
      (show (m : ℝ) + 1 ≤ 2 * m by linarith) 2
    nlinarith only [h]
  nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ C by linarith)]

/-- Total inner-annulus hitting mass. The two terms come from shells within
radius `2*H` and the remaining inverse-square radial tail. -/
theorem inner_annulus_hit_sum_le {k N H L : ℕ} (hk : 2 ≤ k)
    (C : ℝ) (hC : 1 ≤ C) (ordinary : OrdinaryArmWindowInput (k + 1) C) :
    ∑ u ∈ (heartAnnulus (centeredBox (k + 1) N) (centeredBox (k + 1) H) ∩ centeredBox (k + 1) L),
        annulusG (criticalPoint (k + 1)) (centeredBox (k + 1) N) (centeredBox (k + 1) H) u ≤
      (4 * C) * (2 * ((k + 1 : ℕ) : ℝ) * 3 ^ k) *
        (2 * (2 * (H : ℝ) + 1) ^ k + 4 * ((L : ℝ) + 1) ^ (k - 1)) := by
  let S := heartAnnulus (centeredBox (k + 1) N) (centeredBox (k + 1) H) ∩ centeredBox (k + 1) L
  let f (u : Vertex (k + 1)) := (1 : ℝ) / ((linfDist 0 u + 1 - H : ℕ) : ℝ) ^ 2
  let p (u : Vertex (k + 1)) := linfDist 0 u ≤ 2 * H
  let K : ℝ := 2 * ((k + 1 : ℕ) : ℝ) * 3 ^ k
  have hnorm (u : Vertex (k + 1)) (hu : u ∈ S) : H ≤ linfDist 0 u := by
    have hu' := (Finset.mem_inter.mp hu).1
    rw [← sourceAnnulus_eq_heartAnnulus] at hu'
    exact (Finset.mem_filter.mp hu').2
  have hnear : ∑ u ∈ S.filter p, f u ≤ K * (2 * (H : ℝ) + 1) ^ k * 2 := by
    have hsub : S.filter p ⊆ linfBall (0 : Vertex (k + 1)) ((2 * H : ℕ) : ℤ) := by
      intro u hu
      apply (mem_linfBall_iff_dist _ _ (Int.natCast_nonneg _)).mpr
      simpa only [Int.toNat_natCast] using (Finset.mem_filter.mp hu).2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by dsimp [f]; positivity)).trans ?_
    simpa only [f, K, Nat.cast_mul, Nat.cast_ofNat, Nat.add_sub_cancel] using
      (inner_sum_count (show 1 ≤ k + 1 by omega) H (2 * H))
  have hfar : ∑ u ∈ S.filter (fun u => ¬ p u), f u ≤ 4 * (K * ((L : ℝ) + 1) ^ (k - 1)) := by
    let q (u : Vertex (k + 1)) := (1 : ℝ) / ((linfDist 0 u + 1 : ℕ) : ℝ) ^ 2
    have hsub : S.filter (fun u => ¬ p u) ⊆ linfBall (0 : Vertex (k + 1)) (L : ℤ) := by
      intro u hu
      have huL := (Finset.mem_inter.mp (Finset.mem_filter.mp hu).1).2
      rw [← appendix_cube_eq_centeredBox (k + 1) L] at huL
      exact huL
    calc
      _ ≤ ∑ u ∈ S.filter (fun u => ¬ p u), 4 * q u := by
        apply Finset.sum_le_sum
        intro u hu
        have hp : ¬ linfDist 0 u ≤ 2 * H := (Finset.mem_filter.mp hu).2
        have hpos : 0 < linfDist 0 u + 1 - H := by omega
        have hhalf : linfDist 0 u + 1 ≤ 2 * (linfDist 0 u + 1 - H) := by omega
        have hhalfR : ((linfDist 0 u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist 0 u + 1 - H : ℕ) : ℝ) := by
          exact_mod_cast hhalf
        have hposR : (0 : ℝ) < ((linfDist 0 u + 1 - H : ℕ) : ℝ) := by exact_mod_cast hpos
        dsimp [f, q]
        rw [← mul_div_assoc, mul_one]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        simpa only [one_mul] using (show ((linfDist 0 u + 1 : ℕ) : ℝ) ^ 2 ≤
          4 * ((linfDist 0 u + 1 - H : ℕ) : ℝ) ^ 2 by
            have h := pow_le_pow_left₀ (by positivity) hhalfR 2
            nlinarith only [h])
      _ = 4 * ∑ u ∈ S.filter (fun u => ¬ p u), q u := by rw [Finset.mul_sum]
      _ ≤ 4 * ∑ u ∈ linfBall (0 : Vertex (k + 1)) (L : ℤ), q u :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by dsimp [q]; positivity)) (by norm_num)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [q, K, Nat.add_sub_cancel, show k + 1 - 2 = k - 1 by omega] using
          (shell_pow_sum (q := 2) (by omega : 1 ≤ k + 1) (by omega) (0 : Vertex (k + 1)) L)
  change (∑ u ∈ S, _) ≤ (4 * C) * K * _
  calc
    _ ≤ ∑ u ∈ S, (4 * C) * f u := by
      apply Finset.sum_le_sum
      intro u hu
      simpa only [f, ← mul_div_assoc, mul_one,
        show linfDist 0 u + 1 - H = linfDist 0 u - H + 1 by have := hnorm u hu; omega] using
        annulusG_le_ordinary_arm (N := N) (H := H) C hC ordinary u
    _ = (4 * C) * ((∑ u ∈ S.filter p, f u) + ∑ u ∈ S.filter (fun u => ¬ p u), f u) := by
      rw [Finset.sum_filter_add_sum_filter_not, Finset.mul_sum]
    _ ≤ (4 * C) * (K * (2 * (H : ℝ) + 1) ^ k * 2 + 4 * (K * ((L : ℝ) + 1) ^ (k - 1))) :=
      mul_le_mul_of_nonneg_left (add_le_add hnear hfar) (by positivity)
    _ = _ := by ring

end NearCritical.Section8
