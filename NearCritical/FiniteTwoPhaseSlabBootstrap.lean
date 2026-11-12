module

public import NearCritical.FiniteTwoPhaseSlabFamilyInitial
public import NearCritical.FiniteTwoPhaseSlabFamilyDifferential

/-! Actual mixed-slab finite bootstrap. The maximum is only used continuously;
its individual polynomial coordinates supply the derivative bounds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

theorem finiteTwoPhaseBoundaryMaximum_nearCritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ M c ε : ℝ, 0 < M ∧ 0 < c ∧ 0 < ε ∧
      ∀ (q : unitInterval), q ≤ criticalPoint d →
        ∀ (U : Finset (Vertex d)) (m N : ℕ) (p : unitInterval),
          criticalPoint d ≤ p →
          (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m+1 : ℝ)*(N+1 : ℝ)) →
          finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N ≤ 2*M := by
  obtain ⟨M,c,hM,hc,hseed⟩ :=
    finiteTwoPhaseBoundaryMaximum_critical_initial i hB hb hpc pioneers
  let K : ℝ := 1+4*(d : ℝ)*Real.exp c
  have hK : 0 < K := by dsimp [K]; positivity
  let ε : ℝ := min ((1-(criticalPoint d : ℝ))/2) (1/(16*K*M^2))
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεcap : ε ≤ (1-(criticalPoint d : ℝ))/2 := min_le_left _ _
  have hεsmall : 16*K*M^2*ε ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 16*K*M^2 by positivity)).mp
      (show ε ≤ 1/(16*K*M^2) from min_le_right _ _)
    nlinarith
  let P : unitInterval := ⟨((criticalPoint d : ℝ)+1)/2, by
    constructor <;> linarith [(criticalPoint d).2.1,(criticalPoint d).2.2]⟩
  have hP : (P : ℝ) < 1 := by dsimp [P]; linarith
  have hpcP : criticalPoint d ≤ P := by change _ ≤ ((criticalPoint d : ℝ)+1)/2; linarith
  refine ⟨M,c,ε,hM,hc,hε,?_⟩
  intro q hq U m N p hpcp hpwindow
  let H : ℝ := (m+1 : ℝ)*(N+1 : ℝ)
  have hH1 : 1 ≤ H := by
    dsimp [H]
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m),(Nat.cast_nonneg N : (0 : ℝ) ≤ N),
      mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hdelta : H*((p : ℝ)-(criticalPoint d : ℝ)) ≤ ε := by
    have hw : (p : ℝ)-(criticalPoint d : ℝ) ≤ ε/H := by
      dsimp [H]
      linarith
    have hh := (le_div_iff₀ hH).mp hw
    nlinarith
  have hpP : p ≤ P := by
    have hdiff : 0 ≤ (p : ℝ)-(criticalPoint d : ℝ) := sub_nonneg.mpr hpcp
    have hscale := mul_le_mul_of_nonneg_right hH1 hdiff
    change (p : ℝ) ≤ ((criticalPoint d : ℝ)+1)/2
    nlinarith
  have hqP : q ≤ P := hq.trans hpcP
  let f := finiteTwoPhaseBoundaryFamily q c U i (m : ℤ) (N : ℤ)
  have hcoord := finite_family_cubic_bootstrap_of_contDiffOn f hM
    (show 0 ≤ K*H by positivity)
    (fun a ↦ (finiteTwoPhaseBoundaryFamily_contDiff 1 q c U i m N a).contDiffOn)
    (by
      intro a t ht
      let r : unitInterval := ⟨t,⟨(criticalPoint d).2.1.trans ht.1,ht.2.trans p.2.2⟩⟩
      exact finiteTwoPhaseBoundaryFamily_nonneg r q c U i m N a)
    (by
      intro a
      exact (le_finiteFamilyMaximum f a (criticalPoint d : ℝ)).trans (hseed U m N q hq))
    (by
      intro a t ht
      let r : unitInterval := ⟨t,⟨(criticalPoint d).2.1.trans ht.1.le,ht.2.le.trans p.2.2⟩⟩
      have hrP : r ≤ P := ht.2.le.trans hpP
      have hd := finiteTwoPhaseBoundaryFamily_deriv_le_cubic
        r q P hP hrP hqP hq c hc.le U i m N a
      have hmax : 0 ≤ finiteTwoPhaseBoundaryMaximum q c t U i m N :=
        finiteTwoPhaseBoundaryMaximum_nonneg q c t U i m N
      apply hd.trans
      have hk : 4*(d : ℝ)*Real.exp c*(m+1 : ℝ)*(N+1 : ℝ) ≤ K*H := by
        have hbase : 4*(d : ℝ)*Real.exp c ≤ K := by dsimp [K]; linarith
        convert mul_le_mul_of_nonneg_right hbase hH.le using 1 <;> dsimp [H] <;> ring
      exact mul_le_mul_of_nonneg_right hk (pow_nonneg hmax 3))
    (by
      calc
        16*(K*H)*M^2*((p : ℝ)-(criticalPoint d : ℝ)) =
            (16*K*M^2)*(H*((p : ℝ)-(criticalPoint d : ℝ))) := by ring
        _ ≤ (16*K*M^2)*ε := mul_le_mul_of_nonneg_left hdelta (by positivity)
        _ ≤ 1 := hεsmall)
  apply finiteFamilyMaximum_le
  intro a
  exact hcoord (p : ℝ) ⟨hpcp,le_rfl⟩ a

end NearCritical
