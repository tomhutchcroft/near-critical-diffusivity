module

public import NearCritical.SplitCrossDirectOverlap
public import NearCritical.SplitCrossDirectConvolution
public import NearCritical.ThreePointDiagram

/-! Analytic bound for overlaps (item D of the direct proof of
`SplitCrossInput`, analytic estimate).

With `kern e x y := max(1,|x-y|)^(e-d)` (supremum distance):

* `kern_two_mul_le`: `g(a,u) g(u,b) ≤ 2^d g(a,b) (g(a,u) + g(u,b))`, `g = kern 2`;
* `sum_kern_two_two_le`: `Σ_y g(x,y) g(u,y) ≤ K₂ · kern 4 x u` (existing convolution);
* `diagram_le`: the two-vertex diagram
  `Σ_w (Σ_u g(a,u) g(u,b) g(w,u)) · g(a',w) g(w,b')` is at most
  `C · g(a,b) g(a',b') · (kern 6 a a' + kern 6 a b' + kern 6 b a' + kern 6 b b')`;
* **`overlap_le_kern`**: under the sup-norm Green bound (`CriticalSupGreenUpper`,
  from (A)), for tube edges `f, x`,
  `overlap f x ≤ G^5 C · g(a_x,b_x) g(a_f,b_f) · Σ (kern 6 between endpoints)`.

So when the endpoints of the two edges are at mutual distance at least `ρ`, the
overlap is at most `4 G^5 C ρ^(6-d)` times the product of the Green kernels of
the two edges: small for large `ρ` when `d ≥ 7`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory
open scoped Classical BigOperators

variable {d : ℕ}

/-- Regularised power kernel `max(1,|x-y|)^(e-d)`. -/
def kern (e : ℝ) (x y : Vertex d) : ℝ := (max 1 (latticeDistance x y)) ^ (e - (d : ℝ))

lemma kern_nonneg (e : ℝ) (x y : Vertex d) : 0 ≤ kern e x y :=
  Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

lemma kern_comm (e : ℝ) (x y : Vertex d) : kern e x y = kern e y x := by
  unfold kern
  rw [latticeDistance_comm]

theorem kern_two_mul_le (hd : 2 ≤ d) (a u b : Vertex d) :
    kern 2 a u * kern 2 u b ≤ (2 : ℝ) ^ d * kern 2 a b * (kern 2 a u + kern 2 u b) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hγ : (2 : ℝ) - (d : ℝ) ≤ 0 := by linarith
  have hγ' : -(d : ℝ) ≤ (2 : ℝ) - (d : ℝ) := by linarith
  have hA1 : (1 : ℝ) ≤ max 1 (latticeDistance a u) := le_max_left _ _
  have hB1 : (1 : ℝ) ≤ max 1 (latticeDistance u b) := le_max_left _ _
  have hC1 : (1 : ℝ) ≤ max 1 (latticeDistance a b) := le_max_left _ _
  have hCle : max 1 (latticeDistance a b) ≤
      max 1 (latticeDistance a u) + max 1 (latticeDistance u b) := by
    refine max_le (by linarith) ?_
    exact (latticeDistance_triangle a u b).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _))
  have hAu : 0 ≤ kern 2 a u := kern_nonneg _ _ _
  have hub : 0 ≤ kern 2 u b := kern_nonneg _ _ _
  have hab : 0 ≤ kern 2 a b := kern_nonneg _ _ _
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
  have hhalf := half_rpow_le (d := d) (γ := (2 : ℝ) - (d : ℝ)) hC1 hγ'
  have hCpos : 0 < max 1 (latticeDistance a b) / 2 := by linarith
  rcases le_total (max 1 (latticeDistance a b) / 2) (max 1 (latticeDistance a u)) with h | h
  · have h1 : kern 2 a u ≤ (2 : ℝ) ^ d * kern 2 a b :=
      (Real.rpow_le_rpow_of_nonpos hCpos h hγ).trans hhalf
    nlinarith [mul_le_mul_of_nonneg_right h1 hub, mul_nonneg (mul_nonneg h2d hab) hAu]
  · have h' : max 1 (latticeDistance a b) / 2 ≤ max 1 (latticeDistance u b) := by linarith
    have h1 : kern 2 u b ≤ (2 : ℝ) ^ d * kern 2 a b :=
      (Real.rpow_le_rpow_of_nonpos hCpos h' hγ).trans hhalf
    nlinarith [mul_le_mul_of_nonneg_left h1 hAu, mul_nonneg (mul_nonneg h2d hab) hub]

/-- The constant of the Green--Green convolution. -/
def conv2Const (d : ℕ) : ℝ := (4 : ℝ) ^ ((d : ℝ) - 2) * (2 + 19 * (2 * (d : ℝ) * 3 ^ (d - 1)))

lemma conv2Const_nonneg (d : ℕ) : 0 ≤ conv2Const d := by
  unfold conv2Const
  positivity

theorem sum_kern_two_two_le (hd : 5 ≤ d) (s : Finset (Vertex d)) (x u : Vertex d) :
    ∑ y ∈ s, kern 2 x y * kern 2 u y ≤ conv2Const d * kern 4 x u := by
  have h := Section8.truncated_green_convolution_le hd 1 le_rfl s x u
  simpa [kern, conv2Const] using h

/-- The diagram constant. -/
def diagConst (d : ℕ) : ℝ := (2 : ℝ) ^ d * conv2Const d * ((2 : ℝ) ^ d * convConst d)

lemma diagConst_nonneg (d : ℕ) : 0 ≤ diagConst d := by
  unfold diagConst
  exact mul_nonneg (mul_nonneg (by positivity) (conv2Const_nonneg d))
    (mul_nonneg (by positivity) (convConst_nonneg d))

set_option maxHeartbeats 1600000 in
/-- **Two-vertex diagram bound.** -/
theorem diagram_le (hd : 7 ≤ d) (U : Finset (Vertex d)) (a b a' b' : Vertex d) :
    ∑ w ∈ U, (∑ u ∈ U, kern 2 a u * kern 2 u b * kern 2 w u) * (kern 2 a' w * kern 2 w b') ≤
      diagConst d * (kern 2 a b * kern 2 a' b') *
        (kern 6 a a' + kern 6 a b' + kern 6 b a' + kern 6 b b') := by
  have hinner : ∀ w, ∑ u ∈ U, kern 2 a u * kern 2 u b * kern 2 w u ≤
      (2 : ℝ) ^ d * kern 2 a b * (conv2Const d * (kern 4 a w + kern 4 b w)) := by
    intro w
    have h1 : ∀ u ∈ U, kern 2 a u * kern 2 u b * kern 2 w u ≤
        (2 : ℝ) ^ d * kern 2 a b * (kern 2 a u * kern 2 w u + kern 2 b u * kern 2 w u) := by
      intro u _
      have h := mul_le_mul_of_nonneg_right (kern_two_mul_le (by omega) a u b) (kern_nonneg 2 w u)
      have hcomm : kern 2 u b = kern 2 b u := kern_comm 2 u b
      calc kern 2 a u * kern 2 u b * kern 2 w u
          ≤ (2 : ℝ) ^ d * kern 2 a b * (kern 2 a u + kern 2 u b) * kern 2 w u := h
        _ = (2 : ℝ) ^ d * kern 2 a b * (kern 2 a u * kern 2 w u + kern 2 b u * kern 2 w u) := by
            rw [hcomm]
            ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (by positivity) (kern_nonneg _ _ _))
    rw [mul_add]
    exact add_le_add (sum_kern_two_two_le (by omega) U a w) (sum_kern_two_two_le (by omega) U b w)
  have houter : ∀ c : Vertex d, ∑ w ∈ U, kern 4 c w * (kern 2 a' w * kern 2 w b') ≤
      (2 : ℝ) ^ d * kern 2 a' b' * (convConst d * (kern 6 c a' + kern 6 c b')) := by
    intro c
    have h1 : ∀ w ∈ U, kern 4 c w * (kern 2 a' w * kern 2 w b') ≤
        (2 : ℝ) ^ d * kern 2 a' b' * (kern 4 c w * kern 2 a' w + kern 4 c w * kern 2 b' w) := by
      intro w _
      have h := mul_le_mul_of_nonneg_left (kern_two_mul_le (by omega) a' w b')
        (kern_nonneg 4 c w)
      have hcomm : kern 2 w b' = kern 2 b' w := kern_comm 2 w b'
      calc kern 4 c w * (kern 2 a' w * kern 2 w b')
          ≤ kern 4 c w * ((2 : ℝ) ^ d * kern 2 a' b' * (kern 2 a' w + kern 2 w b')) := h
        _ = (2 : ℝ) ^ d * kern 2 a' b' *
            (kern 4 c w * kern 2 a' w + kern 4 c w * kern 2 b' w) := by
            rw [hcomm]
            ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (by positivity) (kern_nonneg _ _ _))
    rw [mul_add]
    have hc1 := fourth_green_convolution_le hd U c a'
    have hc2 := fourth_green_convolution_le hd U c b'
    exact add_le_add (by simpa [kern] using hc1) (by simpa [kern] using hc2)
  have hstep : ∀ w ∈ U, (∑ u ∈ U, kern 2 a u * kern 2 u b * kern 2 w u) *
        (kern 2 a' w * kern 2 w b') ≤
      (2 : ℝ) ^ d * kern 2 a b * conv2Const d *
        (kern 4 a w * (kern 2 a' w * kern 2 w b') + kern 4 b w * (kern 2 a' w * kern 2 w b')) := by
    intro w _
    have h := mul_le_mul_of_nonneg_right (hinner w)
      (mul_nonneg (kern_nonneg 2 a' w) (kern_nonneg 2 w b'))
    calc _ ≤ _ := h
      _ = _ := by ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hpos : 0 ≤ (2 : ℝ) ^ d * kern 2 a b * conv2Const d :=
    mul_nonneg (mul_nonneg (by positivity) (kern_nonneg _ _ _)) (conv2Const_nonneg d)
  refine (mul_le_mul_of_nonneg_left (add_le_add (houter a) (houter b)) hpos).trans (le_of_eq ?_)
  unfold diagConst
  ring

/-- Restricted two-point functions are bounded by the Green kernel. -/
lemma conn_le_kern {G : ℝ} (hG : CriticalSupGreenUpper d G) (S : Set (Vertex d))
    (x y : Vertex d) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent S x {y}) ≤ G * kern 2 x y :=
  (measureReal_mono (connectionToSetEvent_singleton_subset S x y) (measure_ne_top _ _)).trans
    (hG x y)

set_option maxHeartbeats 1600000 in
/-- **Overlap bound.** -/
theorem overlap_le_kern (hd : 7 ≤ d) {G : ℝ} (hG0 : 0 ≤ G) (hG : CriticalSupGreenUpper d G)
    {U : Finset (Vertex d)} (f x : TEdge d U) :
    f.overlap (criticalPoint d) x ≤
      G ^ 5 * diagConst d * (kern 2 x.a x.b * kern 2 f.a f.b) *
        (kern 6 x.a f.a + kern 6 x.a f.b + kern 6 x.b f.a + kern 6 x.b f.b) := by
  refine (overlap_le_diagram (criticalPoint d) f x).trans ?_
  have hterm : ∀ w ∈ U, (∑ u ∈ U,
        (percolation d (criticalPoint d)).real (connectionToSetEvent (U : Set (Vertex d)) x.a {u}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent (U : Set (Vertex d)) u {x.b}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent (U : Set (Vertex d)) w {u})) *
      ((percolation d (criticalPoint d)).real (connectionToSetEvent f.T f.a {w}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent f.T w {f.b})) ≤
      G ^ 5 * ((∑ u ∈ U, kern 2 x.a u * kern 2 u x.b * kern 2 w u) *
        (kern 2 f.a w * kern 2 w f.b)) := by
    intro w _
    have hin : ∑ u ∈ U,
        (percolation d (criticalPoint d)).real (connectionToSetEvent (U : Set (Vertex d)) x.a {u}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent (U : Set (Vertex d)) u {x.b}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent (U : Set (Vertex d)) w {u}) ≤
        G ^ 3 * ∑ u ∈ U, kern 2 x.a u * kern 2 u x.b * kern 2 w u := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun u _ => ?_)
      have h1 := conn_le_kern hG (U : Set (Vertex d)) x.a u
      have h2 := conn_le_kern hG (U : Set (Vertex d)) u x.b
      have h3 := conn_le_kern hG (U : Set (Vertex d)) w u
      have h12 := mul_le_mul h1 h2 measureReal_nonneg (mul_nonneg hG0 (kern_nonneg _ _ _))
      have h123 := mul_le_mul h12 h3 measureReal_nonneg
        (mul_nonneg (mul_nonneg hG0 (kern_nonneg _ _ _)) (mul_nonneg hG0 (kern_nonneg _ _ _)))
      calc _ ≤ _ := h123
        _ = _ := by ring
    have hout : (percolation d (criticalPoint d)).real (connectionToSetEvent f.T f.a {w}) *
        (percolation d (criticalPoint d)).real (connectionToSetEvent f.T w {f.b}) ≤
        G ^ 2 * (kern 2 f.a w * kern 2 w f.b) := by
      have h1 := conn_le_kern hG f.T f.a w
      have h2 := conn_le_kern hG f.T w f.b
      have h12 := mul_le_mul h1 h2 measureReal_nonneg (mul_nonneg hG0 (kern_nonneg _ _ _))
      calc _ ≤ _ := h12
        _ = _ := by ring
    have hsumnn : 0 ≤ G ^ 3 * ∑ u ∈ U, kern 2 x.a u * kern 2 u x.b * kern 2 w u :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun u _ =>
        mul_nonneg (mul_nonneg (kern_nonneg _ _ _) (kern_nonneg _ _ _)) (kern_nonneg _ _ _)))
    have h := mul_le_mul hin hout (mul_nonneg measureReal_nonneg measureReal_nonneg) hsumnn
    calc _ ≤ _ := h
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hdiag := diagram_le hd U x.a x.b f.a f.b
  calc G ^ 5 * ∑ w ∈ U, (∑ u ∈ U, kern 2 x.a u * kern 2 u x.b * kern 2 w u) *
        (kern 2 f.a w * kern 2 w f.b)
      ≤ G ^ 5 * (diagConst d * (kern 2 x.a x.b * kern 2 f.a f.b) *
          (kern 6 x.a f.a + kern 6 x.a f.b + kern 6 x.b f.a + kern 6 x.b f.b)) :=
        mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = _ := by ring

end NearCritical.SplitCrossDirect
end
