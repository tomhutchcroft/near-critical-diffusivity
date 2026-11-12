module
public import NearCritical.AppendixBoxPairLower
public import NearCritical.AppendixBoxClusterSplit
public import NearCritical.AppendixBoxAvoidBudget
public import NearCritical.AppendixBoxSmallScale
public import NearCritical.Section8OutwardSurgery
public import NearCritical.Section8ExtensionEREOne
public import NearCritical.Section8ExtensionTripodError

/-! Per-face-point lower bound in the proof of lem.box_twopoint_lower
(main.tex 6676-6708), for `x` on the face `{z i = -n}` of `Λ_n = centeredBox d n`.

`appendixBoxQ n h i x` is the source box `Q(x)`: height `h` above the face and
transverse half-width `< 2h`, clipped to `Λ_n`. Under the margin hypotheses below it
is contained in `Λ_n` anyway. `appendixBoxF` is its inner face `{z i = -n + h}`.

For every possible cluster `C ⊆ Q(x)` and every `w ∈ C ∩ F` we prove
`c₂(r) n^{2-d} (c_b - K₁ Σ_{v∈C} max(r,|w-v|)^{2-d} - K₂ Σ_{w'∈C∩F} max(r,|w-w'|)^{4-d})
   ≤ P[A_C(w)]`,
with `c_b, K₁, K₂` depending only on `d, α`. The pieces are:
* the accepted outward surgery (`section8_outward_surgery_probability`), eq.lower_surgery;
* eq.lower_step3 (`appendix_box_avoid_lower`);
* esbvkur3 from the cited CH20 input (`appendix_centeredBox_margin_pair_lower`);
* esbvkur from the Green upper bound and the accepted outward-shift kernel bound;
* esbvkur2 from the accepted restricted joint (three-point) error bound, with scale `α n`.
The `w'`-sum includes the diagonal `w' = w`, which the source's E_boundary omits. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Source `Q(x)` for `x` on the face `{z i = -n}`, clipped to `Λ_n`. -/
def appendixBoxQ {d : ℕ} (n h : ℕ) (i : Fin d) (x : Vertex d) : Finset (Vertex d) :=
  (centeredBox d n).filter fun z => z i ≤ -(n : ℤ)+h ∧ ∀ j, j ≠ i → |z j-x j| < 2*(h : ℤ)

/-- The inner face `F` of `Q(x)`. -/
def appendixBoxF {d : ℕ} (n h : ℕ) (i : Fin d) (x : Vertex d) : Finset (Vertex d) :=
  (appendixBoxQ n h i x).filter fun z => z i = -(n : ℤ)+h

lemma appendixBoxQ_subset {d : ℕ} (n h : ℕ) (i : Fin d) (x : Vertex d) :
    appendixBoxQ n h i x ⊆ centeredBox d n := Finset.filter_subset _ _

lemma appendixBoxF_subset {d : ℕ} (n h : ℕ) (i : Fin d) (x : Vertex d) :
    appendixBoxF n h i x ⊆ appendixBoxQ n h i x := Finset.filter_subset _ _

lemma latticeDistance_coord_le {d : ℕ} (a b : Vertex d) (j : Fin d) :
    |(a j : ℝ)-(b j : ℝ)| ≤ latticeDistance a b := by
  simpa only [latticeDistance,vertexReal,Real.dist_eq] using
    dist_le_pi_dist (vertexReal a) (vertexReal b) j

lemma latticeDistance_le_of_coord {d : ℕ} (a b : Vertex d) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ j, |(a j : ℝ)-(b j : ℝ)| ≤ R) : latticeDistance a b ≤ R := by
  change dist (vertexReal a) (vertexReal b) ≤ R
  apply (dist_pi_le_iff hR).mpr
  intro j
  simpa only [vertexReal,Real.dist_eq] using h j

/-- The face-point surgery estimate with independent lower height and upper
transverse scale bounds. This permits the wider slab box used by the
repaired top-face estimate. -/
theorem appendix_box_face_avoid_lower_on_domain {d : ℕ} (hd : 7 ≤ d) (asymp : TwoPointAsymptotics d)
    (lower : RestrictedRectangleLowerInput d) {α β : ℝ} (hβ0 : 0 < β) (hβα : β ≤ α) (hα1 : α ≤ 1) :
    ∃ cb K₁ K₂ : ℝ, 0 < cb ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ (i : Fin d) (n h r : ℕ) (x y : Vertex d) (Q F : Finset (Vertex d)),
      1 ≤ r → β*(n : ℝ)/16 ≤ (h : ℝ) → (h : ℝ) ≤ α*(n : ℝ)/8 → (r : ℝ) ≤ α*(n : ℝ)/16 →
      1 ≤ α*(n : ℝ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      Q ⊆ centeredBox d n → (∀ u ∈ Q, u i ≤ -(n : ℤ) + h) → F ⊆ Q →
      (∀ w ∈ F, w i = -(n : ℤ) + h) →
      (∀ w ∈ F, ∀ j, j ≠ i → |(w j : ℝ) - (x j : ℝ)| ≤ α * (n : ℝ) / 4) →
      ∀ C ⊆ Q, ∀ w ∈ C ∩ F,
      (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1)) *
        ((n : ℝ)^((2 : ℝ)-(d : ℝ)) *
          (cb - K₁*∑ v ∈ C, (max (r : ℝ) (latticeDistance w v))^((2 : ℝ)-(d : ℝ))
              - K₂*∑ w' ∈ C ∩ F,
                  (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)))) ≤
      (percolation d (criticalPoint d)).real
        (appendixBoxAvoidEvent (centeredBox d n) (Q) C
          (C ∩ F) y w) := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymp
  have hα0 : 0 < α := hβ0.trans_le hβα
  have hβ1 : β ≤ 1 := hβα.trans hα1
  let m : ℕ := Nat.ceil (32/β)
  have hm32 : 32/β ≤ (m : ℝ) := Nat.le_ceil _
  have h32 : (32 : ℝ) ≤ 32/β := by
    rw [le_div_iff₀ hβ0]
    nlinarith
  have hm4 : 4 ≤ m := by
    have : (4 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by linarith
  have hβm : 32 ≤ β*(m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm32 hβ0.le
    rwa [mul_div_cancel₀ _ hβ0.ne'] at h
  obtain ⟨cb,hcb,hbox⟩ := appendix_centeredBox_margin_pair_lower (by omega) lower m hm4
  let Cb : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let KJ : ℝ := G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))
  have hKJ : 0 ≤ KJ := by dsimp only [KJ,Cb]; positivity
  have h7α : (0 : ℝ) < 7*α/8 := by linarith
  refine ⟨cb,G^2*(7*α/8)^((2 : ℝ)-(d : ℝ)),KJ*α^((2 : ℝ)-(d : ℝ)),hcb,
    mul_nonneg (sq_nonneg G) (Real.rpow_nonneg h7α.le _),
    mul_nonneg hKJ (Real.rpow_nonneg hα0.le _),?_⟩
  intro i n h r x y Q F hr hh1 hh2 hrα hαn hx hy hQT hQheight hFQ hFheight hFwidth C hCQ w hw
  -- notation and basic real facts
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hn1 : 1 ≤ n := by
    have : (0 : ℕ) < n := by exact_mod_cast hn0
    omega
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hαle : α*(n : ℝ) ≤ n := by nlinarith [mul_le_mul_of_nonneg_right hα1 hn0.le]
  have hαn0 : (0 : ℝ) < α*(n : ℝ) := by linarith
  have hmarg : 2*(n : ℝ)/(m : ℝ) ≤ β*(n : ℝ)/16 := by
    rw [div_le_iff₀ hmpos]
    nlinarith [mul_le_mul_of_nonneg_right hβm hn0.le]
  have hmarg0 : 0 ≤ 2*(n : ℝ)/(m : ℝ) := by positivity
  have hβαn : β * (n : ℝ) ≤ α * (n : ℝ) := mul_le_mul_of_nonneg_right hβα hn0.le
  have hwC := (Finset.mem_inter.mp hw).1
  have hwF := (Finset.mem_inter.mp hw).2
  have hwQ : w ∈ Q := hFQ hwF
  have hwi : w i = -(n : ℤ)+h := hFheight w hwF
  have hwiR : (w i : ℝ) = -(n : ℝ)+h := by exact_mod_cast hwi
  have hQiR (u : Vertex d) (hu : u ∈ Q) : (u i : ℝ) ≤ -(n : ℝ)+h := by
    exact_mod_cast hQheight u hu
  have hyi : -(n : ℝ)+α*(n : ℝ) ≤ (y i : ℝ) := by
    have := (abs_le.mp (hy i)).1
    linarith
  -- the shifted root
  let a : Vertex d := Function.update w i (w i+(r : ℤ))
  have hai : (a i : ℝ) = -(n : ℝ)+h+r := by
    simp only [a,Function.update_self]
    push_cast
    rw [hwiR]
  have haj (j : Fin d) (hj : j ≠ i) : a j = w j := by
    simp only [a,Function.update_apply,hj,if_false]
  -- geometric guards of the surgery
  have hwall : ∀ u ∈ Q, u i ≤ w i := by
    intro u hu
    rw [hwi]
    exact hQheight u hu
  have hWQ : C ∩ F ⊆ Q :=
    fun u hu => hCQ (Finset.mem_inter.mp hu).1
  have hhrn : h+r ≤ n := by
    have : (h : ℝ)+r ≤ n := by linarith
    exact_mod_cast this
  have hIT : section8OutwardSegment w i r ⊆ centeredBox d n := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := (section8_mem_outward_segment w u i r).mp hu
    apply centeredBox_update_mem (hQT hwQ) i
    rw [hwi]
    constructor <;> omega
  have hyseg : y ∉ section8OutwardSegment w i r := by
    intro hu
    obtain ⟨k,hk,hyk⟩ := (section8_mem_outward_segment w y i r).mp hu
    have hyik : y i = w i+(k : ℤ) := by rw [hyk]; simp
    have hyikR : (y i : ℝ) = -(n : ℝ)+h+k := by
      rw [hyik]; push_cast; rw [hwiR]
    have hkR : (k : ℝ) ≤ r := by exact_mod_cast hk
    linarith
  have haT : a ∈ centeredBox d n :=
    hIT ((section8_mem_outward_segment w a i r).mpr ⟨r,le_rfl,rfl⟩)
  -- surgery (eq.lower_surgery) and eq.lower_step3
  have hs := section8_outward_surgery_probability (criticalPoint d) (centeredBox d n)
    (Q) C (C ∩ F) w i r y hwall hWQ hIT hyseg
  have hl := appendix_box_avoid_lower (criticalPoint d) (centeredBox d n)
    (Q) C (C ∩ F) a y haT
  -- esbvkur3: the cited box lower bound at (a, y)
  have hxjR (j : Fin d) (hj : j ≠ i) : |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ) := hx j hj
  have hamarg : ∀ j, -(n : ℝ)+2*(n : ℝ)/(m : ℝ) ≤ (a j : ℝ) ∧
      (a j : ℝ) ≤ (n : ℝ)-2*(n : ℝ)/(m : ℝ) := by
    intro j
    by_cases hj : j = i
    · rw [hj,hai]
      constructor <;> linarith
    · rw [haj j hj]
      have h1 := hFwidth w hwF j hj
      have h2 := hxjR j hj
      have h3 := abs_le.mp h2
      have h4 := abs_le.mp h1
      constructor <;> linarith
  have hymarg : ∀ j, -(n : ℝ)+2*(n : ℝ)/(m : ℝ) ≤ (y j : ℝ) ∧
      (y j : ℝ) ≤ (n : ℝ)-2*(n : ℝ)/(m : ℝ) := by
    intro j
    have h3 := abs_le.mp (hy j)
    constructor <;> linarith
  have hboxlow := hbox n hn1 a y hamarg hymarg
  -- notation for the kernel sums
  let q : ℝ := (2 : ℝ)-(d : ℝ)
  have hq : q ≤ 0 := by dsimp only [q]; linarith
  have hq4 : (4 : ℝ)-(d : ℝ) ≤ 0 := by linarith
  have hnq : 0 ≤ (n : ℝ)^q := Real.rpow_nonneg hn0.le _
  let P := fun u v : Vertex d => (percolation d (criticalPoint d)).real
    (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) u {v})
  have hP0 (u v : Vertex d) : 0 ≤ P u v := measureReal_nonneg
  have hPG (u v : Vertex d) : P u v ≤ G*(max 1 (latticeDistance u v))^q := by
    have h1 : P u v ≤ twoPoint d (criticalPoint d) u v := by
      simpa only [P,Finset.coe_singleton,Finset.sum_singleton] using
        connectionToSet_probability_le_twoPoint_sum (criticalPoint d)
          ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) u {v}
    exact h1.trans (green u v)
  -- esbvkur: the deletion error E1
  have hCT : C ∩ centeredBox d n = C :=
    Finset.inter_eq_left.mpr (fun u hu => hQT (hCQ hu))
  have hE1 : (∑ v ∈ C ∩ centeredBox d n, P a v * P v y) ≤
      (G^2*(7*α/8)^q)*((n : ℝ)^q*
        ∑ v ∈ C, (max (r : ℝ) (latticeDistance w v))^q) := by
    rw [hCT,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have hvQ := hCQ hv
    have hvy : 7*α*(n : ℝ)/8 ≤ max 1 (latticeDistance v y) := by
      have hc := latticeDistance_coord_le v y i
      have hvi := hQiR v hvQ
      have hge : (y i : ℝ)-(v i : ℝ) ≤ |(v i : ℝ)-(y i : ℝ)| := by
        rw [abs_sub_comm]; exact le_abs_self _
      exact le_max_of_le_right (by linarith)
    have hk1 : (max 1 (latticeDistance a v))^q ≤ (max (r : ℝ) (latticeDistance w v))^q :=
      section8_outward_shift_kernel_le w v i r hr (hwall v hvQ) q hq
    have hk2 : (max 1 (latticeDistance v y))^q ≤ (7*α*(n : ℝ)/8)^q :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hvy hq
    have hsplit : (7*α*(n : ℝ)/8)^q = (7*α/8)^q*(n : ℝ)^q := by
      rw [show 7*α*(n : ℝ)/8 = (7*α/8)*(n : ℝ) by ring]
      exact Real.mul_rpow h7α.le hn0.le
    have hk1n : 0 ≤ (max (r : ℝ) (latticeDistance w v))^q :=
      Real.rpow_nonneg (by positivity) _
    have hav := (hPG a v).trans (mul_le_mul_of_nonneg_left hk1 hG.le)
    have hvy' := (hPG v y).trans (mul_le_mul_of_nonneg_left hk2 hG.le)
    rw [hsplit] at hvy'
    calc P a v * P v y
        ≤ (G*(max (r : ℝ) (latticeDistance w v))^q)*(G*((7*α/8)^q*(n : ℝ)^q)) :=
          mul_le_mul hav hvy' (hP0 v y) (mul_nonneg hG.le hk1n)
      _ = G^2*(7*α/8)^q*((n : ℝ)^q*(max (r : ℝ) (latticeDistance w v))^q) := by ring
  -- esbvkur2: the excluded-target joint error E2
  have hE2 : (∑ w' ∈ C ∩ F, (percolation d (criticalPoint d)).real
      (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) a {w'} ∩
       connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) a {y})) ≤
      (KJ*α^q)*((n : ℝ)^q*∑ w' ∈ C ∩ F,
        (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ))) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w' hw'
    have hw'Q := hWQ hw'
    have hw'F := (Finset.mem_inter.mp hw').2
    have hw'i : (w' i : ℝ) = -(n : ℝ)+h := by
      have := hFheight w' hw'F
      exact_mod_cast this
    have haz : α*(n : ℝ)/8 ≤ latticeDistance a y := by
      have hc := latticeDistance_coord_le a y i
      have hge : (y i : ℝ)-(a i : ℝ) ≤ |(a i : ℝ)-(y i : ℝ)| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith [hai]
    have hyz : α*(n : ℝ)/4 ≤ latticeDistance w' y := by
      have hc := latticeDistance_coord_le w' y i
      have hge : (y i : ℝ)-(w' i : ℝ) ≤ |(w' i : ℝ)-(y i : ℝ)| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith [hw'i]
    have hay : max 1 (latticeDistance a w') ≤ 2*(α*(n : ℝ)) := by
      refine max_le (by linarith) ?_
      refine latticeDistance_le_of_coord a w' (R := 2*(α*(n : ℝ))) (by linarith) ?_
      intro j
      by_cases hj : j = i
      · rw [hj,hai,hw'i]
        rw [show -(n : ℝ)+h+r-(-(n : ℝ)+h) = r by ring,abs_of_nonneg (by linarith : (0 : ℝ) ≤ r)]
        linarith
      · rw [haj j hj]
        have h1 := hFwidth w hwF j hj
        have h2 := hFwidth w' hw'F j hj
        have htri : |(w j : ℝ)-(w' j : ℝ)| ≤
            |(w j : ℝ)-(x j : ℝ)|+|(w' j : ℝ)-(x j : ℝ)| := by
          have := abs_sub_le (w j : ℝ) (x j : ℝ) (w' j : ℝ)
          rw [abs_sub_comm (x j : ℝ) (w' j : ℝ)] at this
          exact this
        linarith
    have hj := section8_extension_restricted_joint_error_le (by omega : 5 ≤ d) hG.le green
      (centeredBox d n) a w' y (α*(n : ℝ)) hαn haz hyz hay
    change _ ≤ KJ*(α*(n : ℝ))^q*(max 1 (latticeDistance a w'))^((4 : ℝ)-(d : ℝ)) at hj
    have hk : (max 1 (latticeDistance a w'))^((4 : ℝ)-(d : ℝ)) ≤
        (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)) :=
      section8_outward_shift_kernel_le w w' i r hr (hwall w' hw'Q) _ hq4
    have hsplit : (α*(n : ℝ))^q = α^q*(n : ℝ)^q := Real.mul_rpow hα0.le hn0.le
    rw [hsplit] at hj
    have hcoef : 0 ≤ KJ*(α^q*(n : ℝ)^q) :=
      mul_nonneg hKJ (mul_nonneg (Real.rpow_nonneg hα0.le _) hnq)
    calc _ ≤ KJ*(α^q*(n : ℝ)^q)*(max 1 (latticeDistance a w'))^((4 : ℝ)-(d : ℝ)) := by
          simpa only [mul_assoc] using hj
      _ ≤ KJ*(α^q*(n : ℝ)^q)*(max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)) :=
          mul_le_mul_of_nonneg_left hk hcoef
      _ = _ := by ring
  -- combine
  have hc2 : 0 ≤ (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1)) :=
    pow_nonneg (le_min (criticalPoint d).2.1 (sub_nonneg.mpr (criticalPoint d).2.2)) _
  have hinner : (n : ℝ)^q *
      (cb - G^2*(7*α/8)^q*∑ v ∈ C, (max (r : ℝ) (latticeDistance w v))^q
          - KJ*α^q*∑ w' ∈ C ∩ F,
              (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ))) ≤
      (percolation d (criticalPoint d)).real (section9AvoidanceEvent (centeredBox d n)
        (centeredBox d n) (Q) C {y} (C ∩ F) a) := by
    have hl' := hl
    change P a y - (∑ v ∈ C ∩ centeredBox d n, P a v * P v y) - _ ≤ _ at hl'
    have hboxlow' : cb*(n : ℝ)^q ≤ P a y := hboxlow
    linarith [hl',hboxlow',hE1,hE2]
  calc _ ≤ (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1)) *
        (percolation d (criticalPoint d)).real (section9AvoidanceEvent (centeredBox d n)
          (centeredBox d n) (Q) C {y} (C ∩ F) a) :=
        mul_le_mul_of_nonneg_left hinner hc2
    _ ≤ _ := hs

/-- Per-face-point source lower bound (eq.lower_surgery + eq.lower_step3 + esbvkur,
esbvkur2, esbvkur3), uniform over scales, faces, clusters and face points. -/
theorem appendix_box_face_avoid_lower {d : ℕ} (hd : 7 ≤ d) (asymp : TwoPointAsymptotics d)
    (lower : RestrictedRectangleLowerInput d) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ cb K₁ K₂ : ℝ, 0 < cb ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ (i : Fin d) (n h r : ℕ) (x y : Vertex d),
      1 ≤ r → α*(n : ℝ)/16 ≤ (h : ℝ) → (h : ℝ) ≤ α*(n : ℝ)/8 → (r : ℝ) ≤ α*(n : ℝ)/16 →
      1 ≤ α*(n : ℝ) →
      x i = -(n : ℤ) → (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ)-α*(n : ℝ)) →
      ∀ C ⊆ appendixBoxQ n h i x, ∀ w ∈ C ∩ appendixBoxF n h i x,
      (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1)) *
        ((n : ℝ)^((2 : ℝ)-(d : ℝ)) *
          (cb - K₁*∑ v ∈ C, (max (r : ℝ) (latticeDistance w v))^((2 : ℝ)-(d : ℝ))
              - K₂*∑ w' ∈ C ∩ appendixBoxF n h i x,
                  (max (r : ℝ) (latticeDistance w w'))^((4 : ℝ)-(d : ℝ)))) ≤
      (percolation d (criticalPoint d)).real
        (appendixBoxAvoidEvent (centeredBox d n) (appendixBoxQ n h i x) C
          (C ∩ appendixBoxF n h i x) y w) := by
  obtain ⟨cb, K₁, K₂, hcb, hK₁, hK₂, hface⟩ :=
    appendix_box_face_avoid_lower_on_domain hd asymp lower hα0 le_rfl hα1
  refine ⟨cb, K₁, K₂, hcb, hK₁, hK₂, ?_⟩
  intro i n h r x y hr hhl hhu hrα hαn _hxFace hx hy
  refine hface i n h r x y (appendixBoxQ n h i x) (appendixBoxF n h i x)
    hr hhl hhu hrα hαn hx hy (appendixBoxQ_subset n h i x) ?_
    (appendixBoxF_subset n h i x) ?_ ?_
  · intro u hu
    exact (Finset.mem_filter.mp hu).2.1
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
  · intro w hw j hj
    have hwQ := appendixBoxF_subset n h i x hw
    have hdist := (Finset.mem_filter.mp hwQ).2.2 j hj
    have h' : |(w j : ℝ) - (x j : ℝ)| < 2 * (h : ℝ) := by exact_mod_cast hdist
    linarith

end NearCritical
