module
public import NearCritical.Section9CoalescenceBubble
public import NearCritical.Section8MixedConvolution
public import NearCritical.CriticalTriangle
import Mathlib.Tactic.Abel

/-! The literal seven-edge denominator diagrams have one remaining arm mass.
The constants are derived from finite Green convolutions; no numerical
triangle-squared inequality or diagram estimate is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

/-- The first literal source denominator diagram. -/
def section9SevenEdgeDiagramI {d : ℕ} (U W Z : Finset (Vertex d)) (x : Vertex d) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ U, ∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z,
    twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) u v *
    twoPoint d (criticalPoint d) v z * twoPoint d (criticalPoint d) v w *
    twoPoint d (criticalPoint d) w z * twoPoint d (criticalPoint d) u z' *
    twoPoint d (criticalPoint d) w z'

/-- The second literal source denominator diagram. -/
def section9SevenEdgeDiagramII {d : ℕ} (U W Z : Finset (Vertex d)) (x : Vertex d) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ U, ∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z,
    twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) u v *
    twoPoint d (criticalPoint d) v z * twoPoint d (criticalPoint d) v z' *
    twoPoint d (criticalPoint d) u w * twoPoint d (criticalPoint d) w z *
    twoPoint d (criticalPoint d) w z'

private def sevenGreen {d : ℕ} (k : ℝ) (x y : Vertex d) : ℝ :=
  (max 1 (latticeDistance x y))^(k-(d : ℝ))

private theorem sevenGreen_nonneg {d : ℕ} (k : ℝ) (x y : Vertex d) :
    0 ≤ sevenGreen k x y := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

private theorem seven_distance_shift {d : ℕ} (u w h : Vertex d) :
    latticeDistance (u-h) w = latticeDistance u (w+h) := by
  unfold latticeDistance
  rw [dist_eq_norm,dist_eq_norm]
  congr 1
  funext j
  simp only [Pi.sub_apply,Pi.add_apply,vertexReal,Int.cast_sub,Int.cast_add]
  ring

private theorem seven_distance_difference {d : ℕ} (u h : Vertex d) :
    latticeDistance u (u-h) = latticeDistance 0 h := by
  unfold latticeDistance
  rw [dist_eq_norm,dist_eq_norm]
  have heq : vertexReal u-vertexReal (u-h) = -(vertexReal (0 : Vertex d)-vertexReal h) := by
    funext j
    simp only [Pi.sub_apply,Pi.neg_apply,vertexReal,Pi.zero_apply,Int.cast_zero,Int.cast_sub]
    ring
  rw [heq,norm_neg]

private theorem seven_tau_shift {d : ℕ} (u w h : Vertex d) :
    twoPoint d (criticalPoint d) u (w+h) = twoPoint d (criticalPoint d) (u-h) w := by
  rw [twoPoint_eq_displacement (criticalPoint d) u (w+h),
    twoPoint_eq_displacement (criticalPoint d) (u-h) w]
  congr 1
  abel

private theorem seven_tau_difference {d : ℕ} (w h : Vertex d) :
    twoPoint d (criticalPoint d) (w+h) w = twoPoint d (criticalPoint d) 0 h := by
  rw [twoPoint_symm (criticalPoint d) (w+h) w,
    twoPoint_eq_displacement (criticalPoint d) w (w+h)]
  congr 1
  abel

/-- Reindex finite pairs by their difference, then enlarge only a finite image.
No unrestricted infinite rearrangement is used. -/
private theorem seven_difference_sum_le {d : ℕ} (V W : Finset (Vertex d))
    (F : Vertex d → Vertex d → ℝ) (hF : ∀ v w, 0 ≤ F v w) :
    ∑ v ∈ V, ∑ w ∈ W, F v w ≤
      ∑ h ∈ (V ×ˢ W).image (fun p => p.1-p.2), ∑ w ∈ W, F (w+h) w := by
  let H := (V ×ˢ W).image (fun p => p.1-p.2)
  rw [Finset.sum_comm,Finset.sum_comm (s := H)]
  apply Finset.sum_le_sum
  intro w hw
  let S := V.image (fun v => v-w)
  have heq : (∑ v ∈ V, F v w) = ∑ h ∈ S, F (w+h) w := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      abel
    · intro v _ v' _ hh
      have heq := congrArg (fun a : Vertex d => a+w) hh
      simpa only [sub_add_cancel] using heq
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro h hh
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image.mpr ⟨(v,w),Finset.mem_product.mpr ⟨hv,hw⟩,rfl⟩
  · intro h _ _
    exact hF _ _

private theorem seven_power_mass {d : ℕ} (hd : 9 ≤ d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : Finset (Vertex d)),
      ∑ h ∈ s, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ)) ≤ M := by
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  let M : ℝ := 1+4*J+J/(2*(d : ℝ)-12)
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 2*(d : ℝ)-12 := by linarith
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro s
  let A := s.filter (fun h => latticeDistance 0 h ≤ 1)
  let B := s.filter (fun h => ¬ latticeDistance 0 h ≤ 1)
  have hsplit : (∑ h ∈ s, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ))) =
      (∑ h ∈ A, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ))) +
      ∑ h ∈ B, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ)) := by
    simp only [A,B,Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp
  have hnear : (∑ h ∈ A, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ))) ≤ 1+4*J := by
    calc
      _ ≤ ∑ h ∈ A, (max 1 (latticeDistance 0 h))^((2 : ℝ)-(d : ℝ)) := by
        apply Finset.sum_le_sum
        intro h _
        exact Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
      _ ≤ _ := by
        have hh := Section8.sum_green_ball_le (by omega : 2 ≤ d) 1 A 0
          (fun h hh => by simpa only [Nat.cast_one] using (Finset.mem_filter.mp hh).2)
        convert hh using 1 <;> dsimp only [J] <;> norm_num <;> ring
  have hfar : (∑ h ∈ B, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ))) ≤
      J/(2*(d : ℝ)-12) := by
    have hh := Section8.sum_power_tail_ball_le (by omega : 1 ≤ d) 1 (by decide)
      (12-3*(d : ℝ)) (by linarith) B 0
      (fun h hh => by simpa only [Nat.cast_one] using lt_of_not_ge (Finset.mem_filter.mp hh).2)
    have he : -(d : ℝ)-(12-3*(d : ℝ)) = 2*(d : ℝ)-12 := by ring
    simpa only [Nat.cast_one,Real.one_rpow,mul_one,he,J] using hh
  rw [hsplit]
  exact add_le_add hnear hfar

private theorem seven_distance_pair {d : ℕ} (w h : Vertex d) :
    latticeDistance (w+h) w = latticeDistance 0 h := by
  simpa only [add_sub_cancel_right] using seven_distance_difference (w+h) h

private theorem seven_green_product {d : ℕ} (a b c : ℝ) (h : Vertex d) :
    sevenGreen a 0 h*sevenGreen b 0 h*sevenGreen c 0 h =
      (max 1 (latticeDistance 0 h))^(a+b+c-3*(d : ℝ)) := by
  have hh : 0 < max 1 (latticeDistance 0 h) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  dsimp only [sevenGreen]
  rw [← Real.rpow_add hh,← Real.rpow_add hh]
  congr 1
  ring

private theorem seven_contracted_cores {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ (U W : Finset (Vertex d)) (u : Vertex d),
      (∑ v ∈ U, ∑ w ∈ W,
        twoPoint d (criticalPoint d) u v*twoPoint d (criticalPoint d) v w*
          sevenGreen 4 v w*sevenGreen 4 u w) ≤ K₁ ∧
      (∑ v ∈ U, ∑ w ∈ W,
        twoPoint d (criticalPoint d) u v*twoPoint d (criticalPoint d) u w*
          (sevenGreen 4 v w)^2) ≤ K₂ := by
  let P := twoPoint d (criticalPoint d)
  let Cb : ℝ := G^2*((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))
  let Cm : ℝ := (4 : ℝ)^((d : ℝ)-2)*(82+91*(2*(d : ℝ)*3^(d-1)))
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  obtain ⟨M,hM,hmass⟩ := seven_power_mass hd
  refine ⟨G^2*Cm*M,Cb*M,by positivity,mul_nonneg hCb hM,?_⟩
  intro U W u
  let H := (U ×ˢ W).image (fun p => p.1-p.2)
  have hinnerI (h : Vertex d) :
      (∑ w ∈ W, P (u-h) w*sevenGreen 4 u w) ≤ G*Cm*sevenGreen 6 0 h := by
    calc
      _ ≤ G*(∑ w ∈ W, sevenGreen 4 u w*sevenGreen 2 (u-h) w) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro w _
        have hh := mul_le_mul_of_nonneg_right (green (u-h) w) (sevenGreen_nonneg 4 u w)
        simpa only [P,sevenGreen,mul_assoc,mul_comm,mul_left_comm] using hh
      _ ≤ G*(Cm*sevenGreen 6 u (u-h)) := by
        apply mul_le_mul_of_nonneg_left _ hG
        simpa only [Nat.cast_one,sevenGreen,Cm] using
          Section8.truncated_fourth_green_convolution_le (by omega : 7 ≤ d) 1 (by decide) W u (u-h)
      _ = _ := by simp only [sevenGreen,seven_distance_difference,mul_assoc]
  have hinnerII (h : Vertex d) :
      (∑ w ∈ W, P (u-h) w*P u w) ≤ Cb*sevenGreen 4 0 h := by
    have hh := section9_finite_bubble_le (by omega : 5 ≤ d) hG green W (u-h) u
    have hdistance : latticeDistance (u-h) u = latticeDistance 0 h := by
      rw [latticeDistance_comm]
      exact seven_distance_difference u h
    simpa only [P,Cb,sevenGreen,hdistance,mul_assoc] using hh
  constructor
  · calc
      _ ≤ ∑ h ∈ H, ∑ w ∈ W, P u (w+h)*P (w+h) w*
          sevenGreen 4 (w+h) w*sevenGreen 4 u w :=
        seven_difference_sum_le U W _ (fun v w => by
          exact mul_nonneg (mul_nonneg (mul_nonneg (twoPoint_nonneg _ _ _)
            (twoPoint_nonneg _ _ _)) (sevenGreen_nonneg _ _ _)) (sevenGreen_nonneg _ _ _))
      _ = ∑ h ∈ H, P 0 h*sevenGreen 4 0 h*
          (∑ w ∈ W, P (u-h) w*sevenGreen 4 u w) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        simp only [P,seven_tau_shift,seven_tau_difference,sevenGreen,seven_distance_pair]
        ring
      _ ≤ ∑ h ∈ H, (G^2*Cm)*(max 1 (latticeDistance 0 h))^(12-3*(d : ℝ)) := by
        apply Finset.sum_le_sum
        intro h _
        have hbase : 0 ≤ P 0 h*sevenGreen 4 0 h :=
          mul_nonneg (twoPoint_nonneg _ _ _) (sevenGreen_nonneg _ _ _)
        calc
          _ ≤ P 0 h*sevenGreen 4 0 h*(G*Cm*sevenGreen 6 0 h) :=
            mul_le_mul_of_nonneg_left (hinnerI h) hbase
          _ ≤ (G*sevenGreen 2 0 h)*sevenGreen 4 0 h*(G*Cm*sevenGreen 6 0 h) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (green 0 h) (sevenGreen_nonneg _ _ _))
              (mul_nonneg (mul_nonneg hG hCm) (sevenGreen_nonneg _ _ _))
          _ = (G^2*Cm)*(sevenGreen 2 0 h*sevenGreen 4 0 h*sevenGreen 6 0 h) := by ring
          _ = _ := by rw [seven_green_product]; norm_num
      _ = (G^2*Cm)*(∑ h ∈ H, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmass H) (mul_nonneg (sq_nonneg G) hCm)
  · calc
      _ ≤ ∑ h ∈ H, ∑ w ∈ W, P u (w+h)*P u w*(sevenGreen 4 (w+h) w)^2 :=
        seven_difference_sum_le U W
          (fun v w : Vertex d => P u v*P u w*(sevenGreen 4 v w)^2)
          (fun v w => mul_nonneg
            (mul_nonneg (twoPoint_nonneg (criticalPoint d) u v)
              (twoPoint_nonneg (criticalPoint d) u w)) (sq_nonneg _))
      _ = ∑ h ∈ H, (sevenGreen 4 0 h)^2*(∑ w ∈ W, P (u-h) w*P u w) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        simp only [P,seven_tau_shift,sevenGreen,seven_distance_pair]
        ring
      _ ≤ ∑ h ∈ H, Cb*(max 1 (latticeDistance 0 h))^(12-3*(d : ℝ)) := by
        apply Finset.sum_le_sum
        intro h _
        calc
          _ ≤ (sevenGreen 4 0 h)^2*(Cb*sevenGreen 4 0 h) :=
            mul_le_mul_of_nonneg_left (hinnerII h) (sq_nonneg _)
          _ = Cb*(sevenGreen 4 0 h*sevenGreen 4 0 h*sevenGreen 4 0 h) := by ring
          _ = _ := by rw [seven_green_product]; norm_num
      _ = Cb*(∑ h ∈ H, (max 1 (latticeDistance 0 h))^(12-3*(d : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmass H) hCb

private theorem seven_bubble_cores {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U W Z : Finset (Vertex d)) (u : Vertex d),
      let P := twoPoint d (criticalPoint d)
      let B := fun v w => ∑ z ∈ Z, P v z*P w z
      (∑ v ∈ U, ∑ w ∈ W, P u v*P v w*B v w*B u w) ≤ K ∧
      (∑ v ∈ U, ∑ w ∈ W, P u v*P u w*(B v w)^2) ≤ K := by
  let P := twoPoint d (criticalPoint d)
  let Cb : ℝ := G^2*((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  obtain ⟨K₁,K₂,hK₁,hK₂,hcore⟩ := seven_contracted_cores hd hG green
  refine ⟨Cb^2*(K₁+K₂),mul_nonneg (sq_nonneg _) (add_nonneg hK₁ hK₂),?_⟩
  intro U W Z u P' B
  have hB0 (v w : Vertex d) : 0 ≤ B v w :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (twoPoint_nonneg _ _ _) (twoPoint_nonneg _ _ _))
  have hB (v w : Vertex d) : B v w ≤ Cb*sevenGreen 4 v w := by
    simpa only [B,P',Cb,sevenGreen,mul_assoc] using
      section9_finite_bubble_le (by omega : 5 ≤ d) hG green Z v w
  obtain ⟨hI,hII⟩ := hcore U W u
  constructor
  · calc
      _ ≤ ∑ v ∈ U, ∑ w ∈ W, Cb^2*(P u v*P v w*sevenGreen 4 v w*sevenGreen 4 u w) := by
        apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro w _
        have hA : 0 ≤ P u v*P v w := mul_nonneg (twoPoint_nonneg _ _ _) (twoPoint_nonneg _ _ _)
        calc
          _ ≤ (P u v*P v w)*(Cb*sevenGreen 4 v w)*(Cb*sevenGreen 4 u w) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hB v w) hA) (hB u w)
              (hB0 u w) (mul_nonneg hA (mul_nonneg hCb (sevenGreen_nonneg _ _ _)))
          _ = _ := by ring
      _ = Cb^2*(∑ v ∈ U, ∑ w ∈ W, P u v*P v w*sevenGreen 4 v w*sevenGreen 4 u w) := by
        simp only [Finset.mul_sum]
      _ ≤ Cb^2*K₁ := mul_le_mul_of_nonneg_left hI (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK₂) (sq_nonneg _)
  · calc
      _ ≤ ∑ v ∈ U, ∑ w ∈ W, Cb^2*(P u v*P u w*(sevenGreen 4 v w)^2) := by
        apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro w _
        have hA : 0 ≤ P u v*P u w := mul_nonneg (twoPoint_nonneg _ _ _) (twoPoint_nonneg _ _ _)
        have hs : (B v w)^2 ≤ (Cb*sevenGreen 4 v w)^2 :=
          pow_le_pow_left₀ (hB0 v w) (hB v w) 2
        have hh := mul_le_mul_of_nonneg_left hs hA
        simpa only [mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh
      _ = Cb^2*(∑ v ∈ U, ∑ w ∈ W, P u v*P u w*(sevenGreen 4 v w)^2) := by
        simp only [Finset.mul_sum]
      _ ≤ Cb^2*K₂ := mul_le_mul_of_nonneg_left hII (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK₁) (sq_nonneg _)

/-- Both literal finite seven-edge diagrams are bounded by one actual arm
mass. The constant is uniform in every cutoff and root, and is derived from
(A), finite bubbles and the mixed Green convolution. -/
theorem section9_finite_seven_edge_diagrams_le {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U W Z : Finset (Vertex d)) (x : Vertex d),
      section9SevenEdgeDiagramI U W Z x ≤
        K*(∑ u ∈ U, twoPoint d (criticalPoint d) x u) ∧
      section9SevenEdgeDiagramII U W Z x ≤
        K*(∑ u ∈ U, twoPoint d (criticalPoint d) x u) := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  obtain ⟨K,hK,hcores⟩ := seven_bubble_cores hd hG.le green
  refine ⟨K,hK,?_⟩
  intro U W Z x
  let P := twoPoint d (criticalPoint d)
  let B := fun v w => ∑ z ∈ Z, P v z*P w z
  have hI : section9SevenEdgeDiagramI U W Z x =
      ∑ u ∈ U, P x u*(∑ v ∈ U, ∑ w ∈ W, P u v*P v w*B v w*B u w) := by
    simp only [section9SevenEdgeDiagramI,B,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    dsimp only [P]
    ring
  have hII : section9SevenEdgeDiagramII U W Z x =
      ∑ u ∈ U, P x u*(∑ v ∈ U, ∑ w ∈ W, P u v*P u w*(B v w)^2) := by
    simp only [section9SevenEdgeDiagramII,B,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    dsimp only [P]
    ring
  constructor
  · rw [hI]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    have hh := mul_le_mul_of_nonneg_left (hcores U W Z u).1 (twoPoint_nonneg (criticalPoint d) x u)
    simpa only [P,mul_comm] using hh
  · rw [hII]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    have hh := mul_le_mul_of_nonneg_left (hcores U W Z u).2 (twoPoint_nonneg (criticalPoint d) x u)
    simpa only [P,mul_comm] using hh

end NearCritical
