module
public import NearCritical.Section8RectangleLowerInput
public import NearCritical.LatticeDomain
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Margin-`N/m` generalization of the fixed-shape rectangle grid, for the
cited lem.box_twopoint (CH20 Thm 12, `RestrictedRectangleLowerInput`).

Source main.tex 6702 applies lem.box_twopoint to the moving pair
`(w^{+r}, y)` inside `Λ_n` with margins `≍ α n`. The cited theorem has fixed
aspect ratios, so a finite family of shapes depending only on the margin
ratio is needed. `Section8RectangleGrid` does this for margin `n/16`; here the
grid has `4m` widths and margin `N/m` for any `m ≥ 4`. No probabilistic
statement beyond the cited input is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The `4m` strictly positive aspect ratios of the margin-`N/m` grid. -/
def appendixBoxGridWidth {d : ℕ} (m : ℕ) (κ : Fin d → Fin (4*m)) (j : Fin d) : ℝ :=
  (((κ j).val : ℝ)+1)/(4*(m : ℝ))

theorem appendixBoxGridWidth_pos {d m : ℕ} (hm : 4 ≤ m) (κ : Fin d → Fin (4*m)) (j : Fin d) :
    0 < appendixBoxGridWidth m κ j := by
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  unfold appendixBoxGridWidth
  exact div_pos (by positivity) (by linarith)

private theorem box_grid_rounding (m : ℕ) (hm : 4 ≤ m) (N D : ℝ) (hN : 0 < N)
    (hD : D ≤ N-8*(N/(4*(m : ℝ)))) :
    ∃ k : Fin (4*m),
      max 0 D ≤ ((k.val : ℝ)+1)*(N/(4*(m : ℝ))) ∧
      ((k.val : ℝ)+1)*(N/(4*(m : ℝ))) ≤ max 0 D+2*(N/(4*(m : ℝ))) ∧
      ((k.val : ℝ)+1)/(4*(m : ℝ)) ≤ 1 := by
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  set t : ℝ := N/(4*(m : ℝ)) with htdef
  have h4m : (0 : ℝ) < 4*(m : ℝ) := by linarith
  have ht : 0 < t := by rw [htdef]; exact div_pos hN h4m
  have hNt : 4*(m : ℝ)*t = N := by rw [htdef]; exact mul_div_cancel₀ N h4m.ne'
  have hmt : 4*t ≤ (m : ℝ)*t := mul_le_mul_of_nonneg_right hmR ht.le
  set s : ℝ := max 0 D/t with hsdef
  have hs0 : 0 ≤ s := div_nonneg (le_max_left _ _) ht.le
  have ht0 : t ≠ 0 := ht.ne'
  have hst : s*t = max 0 D := by rw [hsdef]; exact div_mul_cancel₀ _ ht0
  have hDmax : max 0 D ≤ N-8*t := max_le (by linarith) hD
  have hs4 : s ≤ 4*(m : ℝ)-8 := by
    by_contra h
    push_neg at h
    have hh := mul_lt_mul_of_pos_right h ht
    linarith
  obtain hkLow := Nat.le_ceil s
  obtain hkHigh := Nat.ceil_lt_add_one hs0
  have hkm : (Nat.ceil s : ℝ) < 4*(m : ℝ) := by linarith
  have hkmN : Nat.ceil s < 4*m := by exact_mod_cast hkm
  refine ⟨⟨Nat.ceil s,hkmN⟩,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hkLow ht.le
    change max 0 D ≤ ((Nat.ceil s : ℝ)+1)*t
    linarith
  · have hh := mul_le_mul_of_nonneg_right hkHigh.le ht.le
    change ((Nat.ceil s : ℝ)+1)*t ≤ max 0 D+2*t
    linarith
  · change ((Nat.ceil s : ℝ)+1)/(4*(m : ℝ)) ≤ 1
    rw [div_le_one h4m]
    linarith

private theorem box_grid_coordinate (m : ℕ) (hm : 4 ≤ m) (N A Z L U : ℝ) (hN : 0 < N)
    (hwidth : U-L ≤ 1)
    (hAlo : L*N+N/(m : ℝ) ≤ A) (hAhi : A ≤ U*N-N/(m : ℝ))
    (hZlo : L*N+N/(m : ℝ) ≤ Z) (hZhi : Z ≤ U*N-N/(m : ℝ)) :
    ∃ k ℓ : Fin (4*m),
      (-((((k.val : ℝ)+1)/(4*(m : ℝ))))*N ≤ Z-A ∧
        Z-A ≤ ((((ℓ.val : ℝ)+1)/(4*(m : ℝ))))*N) ∧
      (L*N < A-(1+1/(4*(m : ℝ)))*((((k.val : ℝ)+1)/(4*(m : ℝ))))*N) ∧
      (A+(1+1/(4*(m : ℝ)))*((((ℓ.val : ℝ)+1)/(4*(m : ℝ))))*N < U*N) ∧ |Z-A| ≤ N := by
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  set t : ℝ := N/(4*(m : ℝ)) with htdef
  have h4m : (0 : ℝ) < 4*(m : ℝ) := by linarith
  have ht : 0 < t := by rw [htdef]; exact div_pos hN h4m
  have hmt : N/(m : ℝ) = 4*t := by rw [htdef]; ring
  rw [hmt] at hAlo hAhi hZlo hZhi
  have hwN := mul_le_mul_of_nonneg_right hwidth hN.le
  have hgap₁ : A-Z ≤ N-8*t := by nlinarith only [hwN,hAhi,hZlo]
  have hgap₂ : Z-A ≤ N-8*t := by nlinarith only [hwN,hZhi,hAlo]
  obtain ⟨k,hkLow,hkHigh,hk1⟩ := box_grid_rounding m hm N (A-Z) hN hgap₁
  obtain ⟨ℓ,hℓLow,hℓHigh,hℓ1⟩ := box_grid_rounding m hm N (Z-A) hN hgap₂
  rw [← htdef] at hkLow hkHigh hℓLow hℓHigh
  set α : ℝ := ((k.val : ℝ)+1)/(4*(m : ℝ)) with hαdef
  set β : ℝ := ((ℓ.val : ℝ)+1)/(4*(m : ℝ)) with hβdef
  have hαN : α*N = ((k.val : ℝ)+1)*t := by rw [hαdef,htdef]; ring
  have hβN : β*N = ((ℓ.val : ℝ)+1)*t := by rw [hβdef,htdef]; ring
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hαDil : (1+1/(4*(m : ℝ)))*α*N ≤ α*N+t := by
    have he : (1+1/(4*(m : ℝ)))*α*N = α*N+α*t := by rw [htdef]; ring
    have hh := mul_le_mul_of_nonneg_right hk1 ht.le
    rw [he]
    linarith
  have hβDil : (1+1/(4*(m : ℝ)))*β*N ≤ β*N+t := by
    have he : (1+1/(4*(m : ℝ)))*β*N = β*N+β*t := by rw [htdef]; ring
    have hh := mul_le_mul_of_nonneg_right hℓ1 ht.le
    rw [he]
    linarith
  rw [← hαN] at hkLow hkHigh
  rw [← hβN] at hℓLow hℓHigh
  refine ⟨k,ℓ,⟨?_,?_⟩,?_,?_,?_⟩
  · have hh := le_max_right 0 (A-Z)
    change -α*N ≤ Z-A
    linarith
  · change Z-A ≤ β*N
    exact (le_max_right 0 (Z-A)).trans hℓLow
  · change L*N < A-(1+1/(4*(m : ℝ)))*α*N
    rcases le_total Z A with hZA | hAZ
    · rw [max_eq_right (sub_nonneg.mpr hZA)] at hkHigh
      linarith
    · rw [max_eq_left (sub_nonpos.mpr hAZ)] at hkHigh
      linarith
  · change A+(1+1/(4*(m : ℝ)))*β*N < U*N
    rcases le_total A Z with hAZ | hZA
    · rw [max_eq_right (sub_nonneg.mpr hAZ)] at hℓHigh
      linarith
    · rw [max_eq_left (sub_nonpos.mpr hZA)] at hℓHigh
      linarith
  · exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Every moving pair with `N/m` coordinate margins in an ambient rectangle of
width at most `N` belongs to one of finitely many fixed grid shapes, whose
`(1+1/(4m))`-dilation stays inside the OPEN ambient rectangle. -/
theorem appendix_box_grid_cover {d : ℕ} (m : ℕ) (hm : 4 ≤ m) (N : ℕ) (hN : 1 ≤ N)
    (a z : Vertex d) (l u : Fin d → ℝ) (hwidth : ∀ j, u j-l j ≤ 1)
    (ha : ∀ j, l j*(N : ℝ)+(N : ℝ)/(m : ℝ) ≤ (a j : ℝ) ∧
      (a j : ℝ) ≤ u j*(N : ℝ)-(N : ℝ)/(m : ℝ))
    (hz : ∀ j, l j*(N : ℝ)+(N : ℝ)/(m : ℝ) ≤ (z j : ℝ) ∧
      (z j : ℝ) ≤ u j*(N : ℝ)-(N : ℝ)/(m : ℝ)) :
    ∃ κ : (Fin d → Fin (4*m)) × (Fin d → Fin (4*m)),
      z-a ∈ section8Rectangle (appendixBoxGridWidth m κ.1) (appendixBoxGridWidth m κ.2) N ∧
      ((fun w : Vertex d => a+w) '' section8Rectangle
        (fun j => (1+1/(4*(m : ℝ)))*appendixBoxGridWidth m κ.1 j)
        (fun j => (1+1/(4*(m : ℝ)))*appendixBoxGridWidth m κ.2 j) N) ⊆
          {v | ∀ j, l j*(N : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*(N : ℝ)} ∧
      max 1 (latticeDistance 0 (z-a)) ≤ (N : ℝ) := by
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans_le hnR
  have hcoord (j : Fin d) := box_grid_coordinate m hm (N : ℝ) (a j : ℝ) (z j : ℝ)
    (l j) (u j) hn0 (hwidth j) (ha j).1 (ha j).2 (hz j).1 (hz j).2
  choose κ₁ κ₂ hκ using hcoord
  refine ⟨(κ₁,κ₂),?_,?_,?_⟩
  · intro j
    simpa only [appendixBoxGridWidth,Pi.sub_apply,Int.cast_sub] using (hκ j).1
  · rintro v ⟨w,hw,rfl⟩ j
    have hj := hw j
    have hlow := (hκ j).2.1
    have hhigh := (hκ j).2.2.1
    simp only [appendixBoxGridWidth] at hj
    change l j*(N : ℝ) < ((a+w) j : ℝ) ∧ ((a+w) j : ℝ) < u j*(N : ℝ)
    simp only [Pi.add_apply,Int.cast_add]
    constructor <;> nlinarith only [hj.1,hj.2,hlow,hhigh]
  · apply max_le hnR
    change dist (vertexReal (0 : Vertex d)) (vertexReal (z-a)) ≤ (N : ℝ)
    apply (dist_pi_le_iff hn0.le).mpr
    intro j
    simpa only [vertexReal,Pi.zero_apply,Int.cast_zero,Pi.sub_apply,Int.cast_sub,Real.dist_eq,
      zero_sub,abs_neg] using (hκ j).2.2.2

/-- Uniform restricted connection lower bound for moving pairs with `N/m`
margins, from the cited fixed-shape input only. The constant depends on `d,m`. -/
theorem appendix_rectangle_margin_pair_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) (m : ℕ) (hm : 4 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (a z : Vertex d) (l u : Fin d → ℝ),
      (∀ j, u j-l j ≤ 1) →
      (∀ j, l j*(N : ℝ)+(N : ℝ)/(m : ℝ) ≤ (a j : ℝ) ∧
        (a j : ℝ) ≤ u j*(N : ℝ)-(N : ℝ)/(m : ℝ)) →
      (∀ j, l j*(N : ℝ)+(N : ℝ)/(m : ℝ) ≤ (z j : ℝ) ∧
        (z j : ℝ) ≤ u j*(N : ℝ)-(N : ℝ)/(m : ℝ)) →
      c*(N : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent {v : Vertex d | ∀ j,
            l j*(N : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*(N : ℝ)} a {z}) := by
  haveI : NeZero (4*m) := ⟨by omega⟩
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM : (1 : ℝ) < 1+1/(4*(m : ℝ)) := by
    have : (0 : ℝ) < 1/(4*(m : ℝ)) := one_div_pos.mpr (by linarith)
    linarith
  let Shape := (Fin d → Fin (4*m)) × (Fin d → Fin (4*m))
  have hex (κ : Shape) := section8_translated_rectangle_lower lower
    (appendixBoxGridWidth m κ.1) (appendixBoxGridWidth m κ.2)
    (fun j => appendixBoxGridWidth_pos hm κ.1 j)
    (fun j => appendixBoxGridWidth_pos hm κ.2 j)
    (1+1/(4*(m : ℝ))) hM
  let C : Shape → ℝ := fun κ => Classical.choose (hex κ)
  have hC (κ : Shape) : 0 < C κ := (Classical.choose_spec (hex κ)).1
  have hbound (κ : Shape) := (Classical.choose_spec (hex κ)).2
  have hne : (Finset.univ : Finset Shape).Nonempty :=
    ⟨(fun _ => ⟨0,by omega⟩,fun _ => ⟨0,by omega⟩),Finset.mem_univ _⟩
  let c : ℝ := Finset.univ.inf' hne C
  have hc : 0 < c := (Finset.lt_inf'_iff hne).mpr (fun κ _ => hC κ)
  have hcC (κ : Shape) : c ≤ C κ := Finset.inf'_le C (Finset.mem_univ κ)
  refine ⟨c,hc,?_⟩
  intro N hN a z l u hwidth ha hz
  obtain ⟨κ,hinner,hcontain,hdist⟩ := appendix_box_grid_cover m hm N hN a z l u hwidth ha hz
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans_le hnR
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hkpos : 0 < max 1 (latticeDistance 0 (z-a)) := zero_lt_one.trans_le (le_max_left _ _)
  have hkernel : (N : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
      (max 1 (latticeDistance 0 (z-a)))^((2 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hkpos hdist (by linarith)
  have hmono : connectionToSetEvent ((fun v : Vertex d => a+v) ''
        section8Rectangle (fun j => (1+1/(4*(m : ℝ)))*appendixBoxGridWidth m κ.1 j)
          (fun j => (1+1/(4*(m : ℝ)))*appendixBoxGridWidth m κ.2 j) N) a {z} ⊆
      connectionToSetEvent {v : Vertex d | ∀ j,
        l j*(N : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*(N : ℝ)} a {z} := by
    rintro ω ⟨haD,v,hvz,hvD,hav⟩
    refine ⟨hcontain haD,v,hvz,hcontain hvD,hav.mono ?_⟩
    exact fun _ _ h => ⟨h.1,hcontain h.2.1,hcontain h.2.2⟩
  calc
    _ ≤ C κ*(max 1 (latticeDistance 0 (z-a)))^((2 : ℝ)-(d : ℝ)) :=
      mul_le_mul (hcC κ) hkernel (Real.rpow_nonneg hn0.le _) (hC κ).le
    _ ≤ (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((fun u : Vertex d => a+u) ''
          section8Rectangle (fun j => (1+1/(4*(m : ℝ)))*appendixBoxGridWidth m κ.1 j)
            (fun j => (1+1/(4*(m : ℝ)))*appendixBoxGridWidth m κ.2 j) N) a {z}) :=
      hbound κ N hN a z hinner
    _ ≤ _ := measureReal_mono hmono (measure_ne_top _ _)

/-- Source esbvkur3 shape: in the actual cube `Λ_n = centeredBox d n`, every pair
whose coordinates stay at least `2n/m` inside the faces is connected within
`Λ_n` with probability at least `c n^{2-d}`, uniformly in `n` and the pair. -/
theorem appendix_centeredBox_margin_pair_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) (m : ℕ) (hm : 4 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ a z : Vertex d,
      (∀ j, -(n : ℝ)+2*(n : ℝ)/(m : ℝ) ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ (n : ℝ)-2*(n : ℝ)/(m : ℝ)) →
      (∀ j, -(n : ℝ)+2*(n : ℝ)/(m : ℝ) ≤ (z j : ℝ) ∧ (z j : ℝ) ≤ (n : ℝ)-2*(n : ℝ)/(m : ℝ)) →
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) a {z}) := by
  obtain ⟨c₀,hc₀,hbound⟩ := appendix_rectangle_margin_pair_lower hd lower m hm
  have h2pos : (0 : ℝ) < (2 : ℝ)^((2 : ℝ)-(d : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨c₀*(2 : ℝ)^((2 : ℝ)-(d : ℝ)),mul_pos hc₀ h2pos,?_⟩
  intro n hn a z ha hz
  have hN : 1 ≤ 2*n := by omega
  have hcast : ((2*n : ℕ) : ℝ) = 2*(n : ℝ) := by norm_cast
  let l : Fin d → ℝ := fun _ => -(1/2)
  let u : Fin d → ℝ := fun _ => 1/2
  have hwidth : ∀ j, u j-l j ≤ 1 := fun j => by simp only [u,l]; norm_num
  have hmarg (b : Vertex d)
      (hb : ∀ j, -(n : ℝ)+2*(n : ℝ)/(m : ℝ) ≤ (b j : ℝ) ∧ (b j : ℝ) ≤ (n : ℝ)-2*(n : ℝ)/(m : ℝ)) :
      ∀ j, l j*((2*n : ℕ) : ℝ)+((2*n : ℕ) : ℝ)/(m : ℝ) ≤ (b j : ℝ) ∧
        (b j : ℝ) ≤ u j*((2*n : ℕ) : ℝ)-((2*n : ℕ) : ℝ)/(m : ℝ) := by
    intro j
    have e1 : l j*((2*n : ℕ) : ℝ)+((2*n : ℕ) : ℝ)/(m : ℝ) = -(n : ℝ)+2*(n : ℝ)/(m : ℝ) := by
      simp only [l]; rw [hcast]; ring
    have e2 : u j*((2*n : ℕ) : ℝ)-((2*n : ℕ) : ℝ)/(m : ℝ) = (n : ℝ)-2*(n : ℝ)/(m : ℝ) := by
      simp only [u]; rw [hcast]; ring
    rw [e1,e2]
    exact hb j
  have hlow := hbound (2*n) hN a z l u hwidth (hmarg a ha) (hmarg z hz)
  have hsub : {v : Vertex d | ∀ j,
        l j*((2*n : ℕ) : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*((2*n : ℕ) : ℝ)} ⊆
      ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) := by
    intro v hv
    rw [Finset.mem_coe,mem_centeredBox]
    intro j
    have hj := hv j
    simp only [l,u] at hj
    rw [hcast] at hj
    have h1 : (-(n : ℝ)) < (v j : ℝ) := by linarith [hj.1]
    have h2 : (v j : ℝ) < (n : ℝ) := by linarith [hj.2]
    constructor
    · exact_mod_cast h1.le
    · exact_mod_cast h2.le
  have hmono : connectionToSetEvent {v : Vertex d | ∀ j,
        l j*((2*n : ℕ) : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*((2*n : ℕ) : ℝ)} a {z} ⊆
      connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) a {z} := by
    rintro ω ⟨haD,v,hvz,hvD,hav⟩
    refine ⟨hsub haD,v,hvz,hsub hvD,hav.mono ?_⟩
    exact fun _ _ h => ⟨h.1,hsub h.2.1,hsub h.2.2⟩
  have hpow : ((2*n : ℕ) : ℝ)^((2 : ℝ)-(d : ℝ)) =
      (2 : ℝ)^((2 : ℝ)-(d : ℝ))*(n : ℝ)^((2 : ℝ)-(d : ℝ)) := by
    rw [hcast]
    exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)
  rw [hpow] at hlow
  calc c₀*(2 : ℝ)^((2 : ℝ)-(d : ℝ))*(n : ℝ)^((2 : ℝ)-(d : ℝ))
      = c₀*((2 : ℝ)^((2 : ℝ)-(d : ℝ))*(n : ℝ)^((2 : ℝ)-(d : ℝ))) := by ring
    _ ≤ _ := hlow
    _ ≤ _ := measureReal_mono hmono (measure_ne_top _ _)

end NearCritical
