module

public import NearCritical.Section10DifferenceFourier
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! Diffuse entrance bound for the literal independent uniform starts and
paired increment histories in the Section 10 route construction. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

private theorem lazyWeight_nonneg (D : ℕ) (a : Option (Fin D)) :
    0 ≤ lazyCoordinateWeight D a := by
  cases a <;> simp only [lazyCoordinateWeight] <;> positivity

private theorem sum_lazyWeight {D : ℕ} (hD : 0 < D) :
    ∑ a, lazyCoordinateWeight D a = 1 := by
  classical
  rw [Fintype.sum_option]
  simp only [lazyCoordinateWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have h : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp [h] <;> ring

private theorem sum_differenceWeight {D : ℕ} (hD : 0 < D) :
    ∑ a, differenceStepWeight D a = 1 := by
  classical
  unfold differenceStepWeight
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, sum_lazyWeight hD, mul_one]

private theorem sum_historyWeight {D : ℕ} (hD : 0 < D) (T : ℕ) :
    (∑ h : Fin T → Option (Fin D) × Option (Fin D),
      ∏ j, differenceStepWeight D (h j)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : Fin T) a => differenceStepWeight D a)]
  simp only [sum_differenceWeight hD, Finset.prod_const_one]

def differencePrefix (D T : ℕ)
    (h : Fin T → Option (Fin D) × Option (Fin D)) (j : Fin T) : Fin D → ℤ :=
  ∑ t, if t < j then differenceStep D (h t) else 0

/-- The unconditioned finite-history mass of at least one entrance before
time T. The two starts are independent and uniform on S; the history has
the product of the actual difference-increment weights. -/
def diffuseDifferenceEntranceMass (D T : ℕ) (S B : Finset (Fin D → ℤ)) : ℝ := by
  classical
  exact (∑ h : Fin T → Option (Fin D) × Option (Fin D),
    (∏ j, differenceStepWeight D (h j)) *
      ∑ y ∈ S, ((S.filter fun x =>
        ∃ j : Fin T, x-y+differencePrefix D T h j ∈ B).card : ℝ)) / (S.card : ℝ)^2

private theorem entranceStart_card_le {D T : ℕ} (S B : Finset (Fin D → ℤ))
    (y : Fin D → ℤ) (h : Fin T → Option (Fin D) × Option (Fin D)) :
    (S.filter fun x => ∃ j : Fin T, x-y+differencePrefix D T h j ∈ B).card ≤
      T * B.card := by
  classical
  let F := fun j : Fin T => S.filter fun x => x-y+differencePrefix D T h j ∈ B
  have hF (j : Fin T) : (F j).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun x => x-y+differencePrefix D T h j)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x _ z _ he
      have hsub : x-y = z-y := add_right_cancel he
      exact add_right_cancel (by simpa only [sub_eq_add_neg] using hsub : x + -y = z + -y)
  have hsubset : (S.filter fun x => ∃ j : Fin T, x-y+differencePrefix D T h j ∈ B) ⊆
      Finset.univ.biUnion F := by
    intro x hx
    obtain ⟨hxS,j,hj⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hxS,hj⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion F).card := Finset.card_le_card hsubset
    _ ≤ ∑ j, (F j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin T, B.card := Finset.sum_le_sum (fun j _ => hF j)
    _ = _ := by simp

/-- Finite-horizon entrance mass for independent diffuse starts. Each
fixed time and history has at most |B| admissible first starts per second
start, because the displacement is an injective translate of that start. -/
theorem diffuseDifferenceEntranceMass_le {D : ℕ} (hD : 0 < D)
    (T : ℕ) (S B : Finset (Fin D → ℤ)) (hS : S.Nonempty) :
    diffuseDifferenceEntranceMass D T S B ≤ (T : ℝ) * (B.card : ℝ) / (S.card : ℝ) := by
  classical
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  unfold diffuseDifferenceEntranceMass
  calc
    _ ≤ (∑ h : Fin T → Option (Fin D) × Option (Fin D),
        (∏ j, differenceStepWeight D (h j)) *
          ((S.card : ℝ) * ((T : ℝ) * (B.card : ℝ)))) / (S.card : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro h _
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun j _ =>
        mul_nonneg (lazyWeight_nonneg D (h j).1) (lazyWeight_nonneg D (h j).2)))
      calc
        _ ≤ ∑ _y ∈ S, (T : ℝ) * (B.card : ℝ) := by
          apply Finset.sum_le_sum
          intro y _
          exact_mod_cast entranceStart_card_le S B y h
        _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]
    _ = _ := by
      rw [← Finset.sum_mul, sum_historyWeight hD, one_mul]
      field_simp [hSpos.ne'] <;> ring

/-- The exact source starting box B'_M, with transverse dimension D=d−1. -/
def routeStartBox (D M : ℕ) : Finset (Fin D → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc
    ⌈(M : ℝ)/(4*((D : ℝ)+1))⌉ ⌊(M : ℝ)/(2*((D : ℝ)+1))⌋

/-- The literal floor/ceiling box has side at least M/(8(D+1)) for
M≥8(D+1). This controls the diffuse entrance denominator. -/
theorem routeStartBox_card_lower {D M : ℕ} (hM : 8*(D+1) ≤ M) :
    ((M : ℝ)/(8*((D : ℝ)+1)))^D ≤ ((routeStartBox D M).card : ℝ) := by
  let a : ℝ := (M : ℝ)/(4*((D : ℝ)+1))
  let b : ℝ := (M : ℝ)/(2*((D : ℝ)+1))
  let c : ℝ := (M : ℝ)/(8*((D : ℝ)+1))
  have hc : 1 ≤ c := by
    apply (le_div_iff₀ (by positivity : 0 < 8*((D : ℝ)+1))).mpr
    norm_num
    exact_mod_cast hM
  have ha : a = 2*c := by dsimp [a,c]; field_simp <;> ring
  have hb : b = 4*c := by dsimp [b,c]; field_simp <;> ring
  have hr : c ≤ ((⌊b⌋+1-⌈a⌉ : ℤ) : ℝ) := by
    push_cast
    linarith [Int.lt_floor_add_one b, Int.ceil_lt_add_one a]
  have hr0 : 0 ≤ (⌊b⌋+1-⌈a⌉ : ℤ) := by
    exact_mod_cast ((show 0 ≤ c by linarith).trans hr)
  have hrNat : c ≤ ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) := by
    rw [Int.card_Icc]
    have he : (((⌊b⌋+1-⌈a⌉ : ℤ).toNat : ℕ) : ℤ) = ⌊b⌋+1-⌈a⌉ :=
      Int.toNat_of_nonneg hr0
    exact hr.trans_eq (by exact_mod_cast he.symm)
  change c^D ≤ ((Fintype.piFinset (fun _ : Fin D => Finset.Icc ⌈a⌉ ⌊b⌋)).card : ℝ)
  rw [Fintype.card_piFinset_const, Nat.cast_pow]
  exact pow_le_pow_left₀ (by linarith : 0 ≤ c) hrNat D

/-- The entrance mass through time M−1 is O(M^(1−D)), which is the source
M^(2−d) factor. This is before conditioning either route on staying in
the coarse box. -/
theorem sourceRoute_difference_entrance_le {D M : ℕ} (hD : 0 < D)
    (hM : 8*(D+1) ≤ M) (B : Finset (Fin D → ℤ)) :
    diffuseDifferenceEntranceMass D M (routeStartBox D M) B ≤
      (M : ℝ) * (B.card : ℝ) / ((M : ℝ)/(8*((D : ℝ)+1)))^D := by
  have hMp : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have hbase : 0 < ((M : ℝ)/(8*((D : ℝ)+1)))^D := by positivity
  have hcard := routeStartBox_card_lower hM
  have hS : (routeStartBox D M).Nonempty := Finset.card_pos.mp (by
    exact_mod_cast hbase.trans_le hcard)
  exact (diffuseDifferenceEntranceMass_le hD M _ B hS).trans
    (div_le_div_of_nonneg_left (by positivity) hbase hcard)

end NearCritical.Section10
