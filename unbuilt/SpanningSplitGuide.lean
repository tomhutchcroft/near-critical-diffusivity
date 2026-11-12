module

public import NearCritical.SpanningSplitCoupling
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open Filter Set
open scoped Topology Classical

/-- A branch guide from the root to a split channel. It reaches the
transverse center of the channel before reaching the cube's face. -/
def splitBranchGuide {d : ℕ} (f : Fin d × Bool) (pl : Bool) (u : ℝ) : Fin d → ℝ :=
  fun j => if j = f.1 then (if f.2 then 2*u else -(2*u))
    else (if pl then (3/16:ℝ)*min 1 (8*u) else -((3/16:ℝ)*min 1 (8*u)))

theorem splitBranchGuide_height {d : ℕ} (f : Fin d × Bool) (pl : Bool) (u : ℝ) :
    realSpanningHeight f (splitBranchGuide f pl u) = 2*u := by
  obtain ⟨i,s⟩ := f
  cases s <;> simp [realSpanningHeight, splitBranchGuide]

theorem splitBranchGuide_transverse {d : ℕ} (f : Fin d × Bool) (pl : Bool) (u : ℝ)
    {j : Fin d} (hj : j ≠ f.1) :
    realSpanningHeight (j,pl) (splitBranchGuide f pl u) = (3/16:ℝ)*min 1 (8*u) := by
  cases pl <;> simp [realSpanningHeight, splitBranchGuide, hj]

/-- A point in a guide tube stays in the required channel after shifting
the root by any allowed normalized coordinate offset. -/
theorem splitBranchGuide_shift_margins {d : ℕ} (f : Fin d × Bool) (pl : Bool)
    (z s : Fin d → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hz : dist z (splitBranchGuide f pl u) ≤ (1/128:ℝ))
    (hs : ∀ j, |s j| ≤ (1/32:ℝ)) :
    let w := z+s
    (-(1/3:ℝ) ≤ realSpanningHeight f w) ∧
    (∀ j, j ≠ f.1 → |w j| ≤ (1/3:ℝ)) ∧
    ((3/8:ℝ) ≤ realSpanningHeight f w → ∀ j, j ≠ f.1 →
      (9/64:ℝ) ≤ realSpanningHeight (j,pl) w ∧ realSpanningHeight (j,pl) w ≤ 15/64) ∧
    (u = 1 → (7/4:ℝ) ≤ realSpanningHeight f w) := by
  intro w
  let g := splitBranchGuide f pl u
  have hnear (j : Fin d) : |w j - g j| ≤ (5/128:ℝ) := by
    calc
      _ = |(z j - g j) + s j| := by
        change |z j+s j-g j| = _
        congr 1
        ring
      _ ≤ |z j-g j|+|s j| := abs_add_le _ _
      _ ≤ _ := by
        have h := spanning_embedding_coordinate_error hz j
        linarith [hs j]
  have hheight : |realSpanningHeight f w - 2*u| ≤ (5/128:ℝ) := by
    rw [← splitBranchGuide_height f pl u,realSpanningHeight_sub_abs]
    exact hnear f.1
  have hheight' := abs_le.mp hheight
  have hguideWidth (j : Fin d) (hj : j ≠ f.1) : |g j| ≤ (3/16:ℝ) := by
    have hnonneg : 0 ≤ (3/16:ℝ)*min 1 (8*u) :=
      mul_nonneg (by norm_num) (le_min (by norm_num) (by positivity))
    have hle : (3/16:ℝ)*min 1 (8*u) ≤ 3/16 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (8*u))
        (by norm_num : (0:ℝ) ≤ 3/16)
    cases pl <;> simpa [g, splitBranchGuide, hj, abs_of_nonneg hnonneg] using hle
  refine ⟨by linarith [hheight'.1],?_,?_,?_⟩
  · intro j hj
    have h := abs_add_le (w j-g j) (g j)
    rw [sub_add_cancel] at h
    linarith [hnear j,hguideWidth j hj]
  · intro hcut j hj
    have hu' : min 1 (8*u) = 1 := min_eq_left (by linarith [hheight'.2])
    have hsgn : |realSpanningHeight (j,pl) w - (3/16:ℝ)| ≤ (5/128:ℝ) := by
      have he := splitBranchGuide_transverse f pl u hj
      rw [hu',mul_one] at he
      rw [← he,realSpanningHeight_sub_abs]
      exact hnear j
    obtain ⟨hlo,hhi⟩ := abs_le.mp hsgn
    exact ⟨by linarith,by linarith⟩
  · intro h
    linarith [hheight'.1]

/-- A real tree whose embedded branches stay in the guide tubes supplies
the robust channels of the coupling argument for every allowed root shift. -/
def splitSpanningTree_of_branchGuides {d : ℕ} {T : Type} [PseudoMetricSpace T]
    (r : T) (Φ : T → (Fin d → ℝ)) (hΦ : UniformContinuous Φ)
    (hproj : ∀ r y b : T, ∃ a : T,
      dist r a + dist a y = dist r y ∧ 2*dist b a = dist r b + dist b y - dist r y)
    (s : Fin d → ℝ) (hs : ∀ j, |s j| ≤ (1/32:ℝ))
    (hbranches : ∀ (f : Fin d × Bool) (pl : Bool), ∃ y : T,
      dist (Φ y) (splitBranchGuide f pl 1) ≤ (1/128:ℝ) ∧
      ∀ a : T, dist r a + dist a y = dist r y →
        ∃ u : ℝ, 0 ≤ u ∧ dist (Φ a) (splitBranchGuide f pl u) ≤ (1/128:ℝ)) :
    SplitSpanningTree d where
  Tree := T
  metric := inferInstance
  root := r
  embed a := Φ a+s
  continuous := hΦ.add uniformContinuous_const
  projection := hproj
  branches := by
    intro f pl
    obtain ⟨y,hy,hpath⟩ := hbranches f pl
    have htip := splitBranchGuide_shift_margins f pl (Φ y) s 1 (by norm_num) hy hs
    refine ⟨y,htip.2.2.2 rfl,?_⟩
    intro a ha
    obtain ⟨u,hu,hclose⟩ := hpath a ha
    have h := splitBranchGuide_shift_margins f pl (Φ a) s u hu hclose hs
    exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- Normalized root offsets in the allowed box have a subsequential
limit in the same closed transverse range. -/
theorem split_root_offsets_tendsto_subseq {d : ℕ} (t : ℕ → ℕ) (o : ℕ → Vertex d)
    (ho : ∀ n, o n ∈ centeredBox d ((t n-1)/32)) :
    ∃ s : Fin d → ℝ, (∀ j, |s j| ≤ (1/32:ℝ)) ∧
      ∃ sub : ℕ → ℕ, StrictMono sub ∧
        Tendsto (fun n => scaledSpanningVertex (t (sub n)) (o (sub n))) atTop (𝓝 s) := by
  let Q : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-(1/32:ℝ)) (1/32))
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem (n : ℕ) : scaledSpanningVertex (t n) (o n) ∈ Q := by
    intro j _
    apply abs_le.mp
    change |(o n j:ℝ)/(t n:ℝ)| ≤ (1/32:ℝ)
    by_cases ht : t n = 0
    · simp [ht]
    have hpos : 0 < (t n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht
    have hcoord := abs_le.mpr (mem_centeredBox.mp (ho n) j)
    have hcoord' : |(o n j:ℝ)| ≤ (((t n-1)/32:ℕ):ℝ) := by exact_mod_cast hcoord
    have hside : 32*(((t n-1)/32:ℕ):ℝ) ≤ (t n:ℝ) := by
      exact_mod_cast (show 32*((t n-1)/32) ≤ t n by omega)
    rw [abs_div, abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (by linarith)
  obtain ⟨s,hs,sub,hsub,htend⟩ := hQ.tendsto_subseq hmem
  exact ⟨s,fun j => abs_le.mpr (hs j (Set.mem_univ j)),sub,hsub,htend⟩

/-- Passing from an embedding centered at the root to absolute lattice
coordinates adds only the error in the normalized root offset. -/
theorem scaledSpanningVertex_dist_shift_le {d : ℕ} (t : ℕ) (x o : Vertex d)
    (a s : Fin d → ℝ) :
    dist (scaledSpanningVertex t x) (a+s) ≤
      dist (scaledSpanningVertex t (x-o)) a + dist (scaledSpanningVertex t o) s := by
  apply (dist_pi_le_iff (add_nonneg dist_nonneg dist_nonneg)).mpr
  intro j
  have h₁ := dist_le_pi_dist (scaledSpanningVertex t (x-o)) a j
  have h₂ := dist_le_pi_dist (scaledSpanningVertex t o) s j
  rw [Real.dist_eq] at h₁ h₂ ⊢
  have he : scaledSpanningVertex t (x-o) j =
      scaledSpanningVertex t x j - scaledSpanningVertex t o j := by
    simp only [scaledSpanningVertex,Pi.sub_apply,Int.cast_sub,sub_div]
  rw [he] at h₁
  rw [show scaledSpanningVertex t x j - (a+s) j =
      (scaledSpanningVertex t x j-scaledSpanningVertex t o j-a j) +
        (scaledSpanningVertex t o j-s j) by simp only [Pi.add_apply]; ring]
  exact (abs_add_le _ _).trans (add_le_add h₁ h₂)

/-- Removing the distinct-vertex correction from the chemical metric
of the cited scaling limit changes distortion by at most the metric scale. -/
theorem chemical_distortion_le_of_corrected {V : Type*} {G : SimpleGraph V}
    (x y : V) {c u ε : ℝ} (hc : 0 ≤ c)
    (h : |c*((G.dist x y:ℝ) + (if x = y then 0 else 1))-u| ≤ ε) :
    |c*(G.dist x y:ℝ)-u| ≤ ε+c := by
  classical
  by_cases he : x = y
  · have h' : |c*(G.dist x y:ℝ)-u| ≤ ε := by simpa [he] using h
    exact h'.trans (le_add_of_nonneg_right hc)
  · have h' : |c*((G.dist x y:ℝ)+1)-u| ≤ ε := by simpa only [if_neg he] using h
    calc
      _ = |(c*((G.dist x y:ℝ)+1)-u) + (-c)| := by congr 1; ring
      _ ≤ |c*((G.dist x y:ℝ)+1)-u| + |-c| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg,abs_of_nonneg hc]; exact add_le_add_right h' _

/-- A correspondence stated for embeddings centered at the root
gives the absolute-coordinate approximation when the root offset converges. -/
theorem SplitSpanningTree.eventually_approximatedBy_of_centered {d : ℕ} (L : SplitSpanningTree d)
    (s : Fin d → ℝ) (t : ℕ → ℕ) (o : ℕ → Vertex d) (ω : ℕ → Configuration d) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hshift : Tendsto (fun n => scaledSpanningVertex (t n) (o n)) atTop (𝓝 s))
    (hcenter : letI := L.metric
      ∀ᶠ n in atTop, ∃ (c : ℝ) (R : Vertex d → L.Tree → Prop), 0 ≤ c ∧ R (o n) L.root ∧
        (∀ x a, R x a → (openGraph (ω n)).Reachable (o n) x) ∧
        (∀ x, (openGraph (ω n)).Reachable (o n) x → ∃ a, R x a) ∧
        (∀ a, ∃ x, R x a) ∧
        (∀ x a x' a', R x a → R x' a' →
          |c*((openGraph (ω n)).dist x x':ℝ)-dist a a'| ≤ ε n) ∧
        (∀ x a, R x a → dist (scaledSpanningVertex (t n) (x-o n)) (L.embed a-s) ≤ ε n)) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, L.approximatedBy (t n) (o n) (ω n) (ε' n) := by
  letI := L.metric
  let e (n : ℕ) := dist (scaledSpanningVertex (t n) (o n)) s
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, dist_self] using hshift.dist (tendsto_const_nhds (x := s))
  refine ⟨fun n => ε n+e n, by simpa only [zero_add] using hε.add he, ?_⟩
  filter_upwards [hcenter] with n hn
  obtain ⟨c,R,hc,hroot,hR,hcover,hsurj,hdist,hembed⟩ := hn
  refine ⟨c,R,hc,hroot,hR,hcover,hsurj,?_,?_⟩
  · intro x a x' a' hx hx'
    exact (hdist x a x' a' hx hx').trans (le_add_of_nonneg_right dist_nonneg)
  · intro x a hx
    have h := scaledSpanningVertex_dist_shift_le (t n) x (o n) (L.embed a-s) s
    rw [sub_add_cancel] at h
    exact h.trans (add_le_add_right (hembed x a hx) _)

end NearCritical.Section10
