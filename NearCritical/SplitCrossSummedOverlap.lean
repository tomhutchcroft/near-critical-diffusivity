module

public import NearCritical.SplitCrossDirectOverlapBound

/-! Sum over both terminal choices before estimating the two-vertex
overlap diagram. An interior endpoint can be represented by a singleton. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical BigOperators

def restrictedConnectionReal {d : ℕ} (p : unitInterval) (S : Set (Vertex d))
    (a b : Vertex d) : ℝ :=
  (percolation d p).real (connectionToSetEvent S a {b})

def summedEndpointKernel {d : ℕ} (p : unitInterval) (S : Set (Vertex d))
    (a : Vertex d) (Y : Finset (Vertex d)) (u : Vertex d) : ℝ :=
  restrictedConnectionReal p S a u * ∑ z ∈ Y, restrictedConnectionReal p S u z

theorem summedEndpointKernel_nonneg {d : ℕ} (p : unitInterval) (S : Set (Vertex d))
    (a : Vertex d) (Y : Finset (Vertex d)) (u : Vertex d) :
    0 ≤ summedEndpointKernel p S a Y u :=
  mul_nonneg measureReal_nonneg (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))

/-- The two terminal sets may be summed independently. Both terminal
factors may be bounded by the first moment in the ambient box. -/
theorem sum_overlap_le_diagram {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (Yf Yx : Finset (Vertex d)) (af ax : Vertex d)
    (f x : Vertex d → TEdge d U)
    (hf : ∀ y ∈ Yf, (f y).a = af ∧ (f y).b = y)
    (hx : ∀ y ∈ Yx, (x y).a = ax ∧ (x y).b = y) :
    (∑ y ∈ Yf, ∑ z ∈ Yx, (f y).overlap p (x z)) ≤
      ∑ w ∈ U, (∑ u ∈ U, summedEndpointKernel p (U : Set (Vertex d)) ax Yx u *
        restrictedConnectionReal p (U : Set (Vertex d)) w u) *
          summedEndpointKernel p (U : Set (Vertex d)) af Yf w := by
  let τ := restrictedConnectionReal p (U : Set (Vertex d))
  let A (z w : Vertex d) := ∑ u ∈ U, τ ax u * τ u z * τ w u
  let B (y w : Vertex d) := τ af w * τ w y
  have hpoint (y z : Vertex d) (hy : y ∈ Yf) (hz : z ∈ Yx) :
      (f y).overlap p (x z) ≤ ∑ w ∈ U, A z w * B y w := by
    refine (overlap_le_diagram p (f y) (x z)).trans (Finset.sum_le_sum (fun w _ => ?_))
    obtain ⟨hfa, hfb⟩ := hf y hy
    obtain ⟨hxa, hxb⟩ := hx z hz
    rw [hfa, hfb, hxa, hxb]
    change A z w * (restrictedConnectionReal p (f y).T af w *
      restrictedConnectionReal p (f y).T w y) ≤ A z w * B y w
    have hmono (a b : Vertex d) : restrictedConnectionReal p (f y).T a b ≤ τ a b :=
      measureReal_mono (connectionToSetEvent_mono (f y).hT subset_rfl a) (measure_ne_top _ _)
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul (hmono af w) (hmono w y) measureReal_nonneg measureReal_nonneg
    · exact Finset.sum_nonneg (fun _ _ =>
        mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg)
  have hsumA (w : Vertex d) : (∑ z ∈ Yx, A z w) =
      ∑ u ∈ U, summedEndpointKernel p (U : Set (Vertex d)) ax Yx u * τ w u := by
    simp only [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    change _ = (τ ax u * ∑ z ∈ Yx, τ u z) * τ w u
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsumB (w : Vertex d) : (∑ y ∈ Yf, B y w) =
      summedEndpointKernel p (U : Set (Vertex d)) af Yf w := by
    simp only [B, summedEndpointKernel, τ, Finset.mul_sum]
  calc
    _ ≤ ∑ y ∈ Yf, ∑ z ∈ Yx, ∑ w ∈ U, A z w * B y w :=
      Finset.sum_le_sum (fun y hy => Finset.sum_le_sum (fun z hz => hpoint y z hy hz))
    _ = ∑ w ∈ U, (∑ z ∈ Yx, A z w) * (∑ y ∈ Yf, B y w) := by
      simp_rw [Finset.sum_comm (s := Yx) (t := U)]
      rw [Finset.sum_comm (s := Yf) (t := U)]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_mul_sum, Finset.sum_comm (s := Yx) (t := Yf)]
    _ = _ := by simp only [hsumA, hsumB, τ]

private theorem restrictedConnectionReal_le_kern {d : ℕ} {G : ℝ} (green : CriticalSupGreenUpper d G)
    (S : Set (Vertex d)) (a b : Vertex d) :
    restrictedConnectionReal (criticalPoint d) S a b ≤ G * kern 2 a b :=
  (measureReal_mono (connectionToSetEvent_singleton_subset S a b) (measure_ne_top _ _)).trans
    (green a b)

/-- With a single interior endpoint, the two-factor product can be
estimated by two kernels centered at its endpoints. -/
theorem summedEndpointKernel_singleton_le {d : ℕ} (hd : 2 ≤ d) {G : ℝ} (hG : 0 ≤ G)
    (green : CriticalSupGreenUpper d G) (S : Set (Vertex d)) (a b u : Vertex d) (hne : a ≠ b) :
    summedEndpointKernel (criticalPoint d) S a {b} u ≤
      ((2 : ℝ)^d * G^2 * kern 2 a b) * (∑ z ∈ ({a,b} : Finset (Vertex d)), kern 2 z u) := by
  simp only [summedEndpointKernel, Finset.sum_singleton]
  calc
    _ ≤ (G * kern 2 a u) * (G * kern 2 u b) :=
      mul_le_mul (restrictedConnectionReal_le_kern green S a u)
        (restrictedConnectionReal_le_kern green S u b) measureReal_nonneg
        (mul_nonneg hG (kern_nonneg _ _ _))
    _ = G^2 * (kern 2 a u * kern 2 u b) := by ring
    _ ≤ G^2 * ((2 : ℝ)^d * kern 2 a b * (kern 2 a u + kern 2 u b)) :=
      mul_le_mul_of_nonneg_left (kern_two_mul_le hd a u b) (sq_nonneg G)
    _ = _ := by
      rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton, kern_comm 2 u b]
      ring

/-- A terminal set of bounded first moment leaves one kernel centered at
the other endpoint. -/
theorem summedEndpointKernel_le_of_mass {d : ℕ} {G B : ℝ} (hG : 0 ≤ G)
    (green : CriticalSupGreenUpper d G) (S : Set (Vertex d))
    (a u : Vertex d) (Y : Finset (Vertex d))
    (hY : ∑ z ∈ Y, restrictedConnectionReal (criticalPoint d) S u z ≤ B) :
    summedEndpointKernel (criticalPoint d) S a Y u ≤
      (G * B) * ∑ z ∈ ({a} : Finset (Vertex d)), kern 2 z u := by
  rw [summedEndpointKernel, Finset.sum_singleton]
  calc
    _ ≤ (G * kern 2 a u) * B :=
      mul_le_mul (restrictedConnectionReal_le_kern green S a u) hY
        (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))
        (mul_nonneg hG (kern_nonneg _ _ _))
    _ = _ := by ring

/-- The two Green convolutions apply to any endpoint majorants of the
summed diagram. This includes two interior, one face, or two face edges. -/
theorem summed_overlap_diagram_le {d : ℕ} (hd : 7 ≤ d) {G Lx Lf : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) (hLx : 0 ≤ Lx) (hLf : 0 ≤ Lf)
    (U Yf Yx X F : Finset (Vertex d)) (af ax : Vertex d)
    (hx : ∀ u ∈ U, summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) ax Yx u ≤
      Lx * ∑ a ∈ X, kern 2 a u)
    (hf : ∀ w ∈ U, summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) af Yf w ≤
      Lf * ∑ b ∈ F, kern 2 b w) :
    (∑ w ∈ U, (∑ u ∈ U, summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) ax Yx u *
      restrictedConnectionReal (criticalPoint d) (U : Set (Vertex d)) w u) *
      summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) af Yf w) ≤
    (((Lx * G) * conv2Const d) * Lf) * convConst d * ∑ a ∈ X, ∑ b ∈ F, kern 6 a b := by
  let τ := restrictedConnectionReal (criticalPoint d) (U : Set (Vertex d))
  let Kx := summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) ax Yx
  let Kf := summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) af Yf
  let A (w : Vertex d) := ∑ a ∈ X, kern 4 a w
  let B (w : Vertex d) := ∑ b ∈ F, kern 2 b w
  let H := (Lx * G) * conv2Const d
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hLx hG) (conv2Const_nonneg d)
  have hA (w : Vertex d) : 0 ≤ A w := Finset.sum_nonneg (fun _ _ => kern_nonneg _ _ _)
  have hinner (w : Vertex d) : (∑ u ∈ U, Kx u * τ w u) ≤ H * A w := by
    calc
      _ ≤ ∑ u ∈ U, (Lx * ∑ a ∈ X, kern 2 a u) * (G * kern 2 w u) := by
        apply Finset.sum_le_sum
        intro u hu
        exact mul_le_mul (hx u hu) (restrictedConnectionReal_le_kern green _ w u)
          measureReal_nonneg (mul_nonneg hLx (Finset.sum_nonneg (fun _ _ => kern_nonneg _ _ _)))
      _ = (Lx * G) * ∑ a ∈ X, ∑ u ∈ U, kern 2 a u * kern 2 w u := by
        rw [Finset.sum_comm (s := X) (t := U), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_mul]
        ring
      _ ≤ H * A w := by
        unfold H A
        rw [mul_assoc (Lx * G) (conv2Const d), Finset.mul_sum (a := conv2Const d)]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun a _ => sum_kern_two_two_le (by omega) U a w))
          (mul_nonneg hLx hG)
  have houter :
      (∑ w ∈ U, A w * B w) ≤ convConst d * ∑ a ∈ X, ∑ b ∈ F, kern 6 a b := by
    calc
      _ = ∑ a ∈ X, ∑ b ∈ F, ∑ w ∈ U, kern 4 a w * kern 2 b w := by
        simp only [A, B, Finset.sum_mul_sum]
        rw [Finset.sum_comm (s := U) (t := X)]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm (s := U) (t := F)]
      _ ≤ ∑ a ∈ X, ∑ b ∈ F, convConst d * kern 6 a b := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        exact fourth_green_convolution_le hd U a b
      _ = _ := by simp_rw [Finset.mul_sum]
  change (∑ w ∈ U, (∑ u ∈ U, Kx u * τ w u) * Kf w) ≤ _
  calc
    _ ≤ ∑ w ∈ U, (H * A w) * (Lf * B w) := by
      apply Finset.sum_le_sum
      intro w hw
      exact mul_le_mul (hinner w) (hf w hw) (summedEndpointKernel_nonneg _ _ _ _ _)
        (mul_nonneg hH (hA w))
    _ = (H * Lf) * ∑ w ∈ U, A w * B w := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (H * Lf) * (convConst d * ∑ a ∈ X, ∑ b ∈ F, kern 6 a b) :=
      mul_le_mul_of_nonneg_left houter (mul_nonneg hH hLf)
    _ = _ := by rw [mul_assoc (H * Lf) (convConst d)]

end NearCritical.SplitCrossDirect
