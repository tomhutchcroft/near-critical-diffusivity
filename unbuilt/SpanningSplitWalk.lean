module

public import NearCritical.Section10SplitLowerCount
public import NearCritical.SpanningChemicalCorrespondence

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- A nearest-neighbour open walk reaches an intermediate signed height
exactly. Its prefix up to the first such vertex stays at or below that height. -/
theorem openWalk_prefix_at_height {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (w : (openGraph ω).Walk x y) (f : Fin d × Bool) (H : ℤ)
    (hx : faceHeight f x ≤ H) (hy : H ≤ faceHeight f y) :
    ∃ (v : Vertex d) (p : (openGraph ω).Walk x v),
      faceHeight f v = H ∧ (∀ z ∈ p.support, faceHeight f z ≤ H) ∧
        p.support ⊆ w.support := by
  revert hx hy
  induction w with
  | nil =>
    intro hx hy
    refine ⟨_, .nil, le_antisymm hx hy, ?_, fun _ h => h⟩
    intro z hz
    simpa only [SimpleGraph.Walk.mem_support_nil_iff.mp hz] using hx
  | @cons a b c hab w ih =>
    intro hx hy
    by_cases ha : faceHeight f a = H
    · refine ⟨a, .nil, ha, ?_, ?_⟩
      · intro z hz
        simpa only [SimpleGraph.Walk.mem_support_nil_iff.mp hz] using hx
      · intro z hz
        exact List.mem_cons.mpr (Or.inl (SimpleGraph.Walk.mem_support_nil_iff.mp hz))
    · have hab' : (openGraph (fun _ : Bond d => true)).Adj a b := by
        obtain ⟨e,_,he⟩ := hab
        exact ⟨e,rfl,he⟩
      obtain ⟨j,hstep,hrest⟩ := latticeAdj_coords hab'
      have hstep' : faceHeight f b ≤ faceHeight f a + 1 := by
        obtain ⟨i,s⟩ := f
        by_cases hij : i = j
        · subst i
          cases s <;> simp [faceHeight] <;> omega
        · have he := hrest i hij
          cases s <;> simp [faceHeight] <;> omega
      obtain ⟨v,p,hv,hp,hsub⟩ := ih (by omega) hy
      refine ⟨v, p.cons hab, hv, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hp z hz
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (hsub hz)

/-- A walk following a split channel to at least its far height gives the
exact crossing event used by the split-count argument. Inside the cube no
transverse split restriction is needed. -/
theorem crossSplit_of_walk_channel {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (w : (openGraph ω).Walk x y) (t R : ℕ) (f : Fin d × Bool) (pl : Bool)
    (ht : 1 ≤ t) (hR : 0 < R)
    (hx : x ∈ typicalCube t (0 : Vertex d))
    (hy : ((t - 1) / 2 : ℕ) + (R : ℤ) ≤ faceHeight f y)
    (hlower : ∀ z ∈ w.support, -(((t - 1) / 2 : ℕ) : ℤ) ≤ faceHeight f z)
    (hwidth : ∀ z ∈ w.support, ∀ j, j ≠ f.1 → |z j| ≤ (((t - 1) / 2 : ℕ) : ℤ))
    (hsplit : ∀ z ∈ w.support, (((t - 1) / 2 : ℕ) : ℤ) < faceHeight f z →
      ∀ j, j ≠ f.1 → splitRange t pl (z j)) :
    ω ∈ crossSplit t f pl R x := by
  let N := (t - 1) / 2
  have hx' : faceHeight f x ≤ (N : ℤ) := by
    have h := (mem_typicalCube_iff_int ht 0 x).mp hx f.1
    obtain ⟨i,s⟩ := f
    simp only [Pi.zero_apply, sub_zero] at h
    cases s <;> simp [faceHeight] <;> omega
  obtain ⟨v,p,hv,hp,hsub⟩ := openWalk_prefix_at_height w f ((N:ℤ)+R) (by omega) hy
  have hBeyond (z : Vertex d) (hz : z ∈ p.support) (hheight : (N:ℤ) < faceHeight f z) :
      z ∈ splitBeyond t f pl R := by
    refine Finset.mem_filter.mpr ⟨?_, hheight, hsplit z (hsub hz) hheight⟩
    rw [mem_centeredBox]
    intro j
    have h₁ := hlower z (hsub hz)
    have h₂ := hp z hz
    by_cases hj : j = f.1
    · subst j
      obtain ⟨i,s⟩ := f
      cases s <;> simp [faceHeight] at h₁ h₂ <;> omega
    · have h := abs_le.mp (hwidth z (hsub hz) j hj)
      omega
  refine ⟨v, Finset.mem_filter.mpr ⟨hBeyond v p.end_mem_support (by omega), hv⟩, p, ?_⟩
  intro z hz
  refine Finset.mem_union.mpr ?_
  by_cases h : (N:ℤ) < faceHeight f z
  · exact Or.inr (hBeyond z hz h)
  · refine Or.inl ((mem_typicalCube_iff_int ht 0 z).mpr ?_)
    intro j
    simp only [Pi.zero_apply, sub_zero]
    by_cases hj : j = f.1
    · subst j
      have h₁ := hlower z (hsub hz)
      obtain ⟨i,s⟩ := f
      cases s <;> simp [faceHeight] at h₁ h <;> omega
    · exact abs_le.mp (hwidth z (hsub hz) j hj)

/-- Coordinate margins for a limiting split channel. The branch can
move transversely within the central cube. Once its signed height reaches
three eighths of the scale, it stays in the appropriate split interval. -/
theorem split_channel_coordinates {d t : ℕ} (ht : 1 ≤ t) (f : Fin d × Bool) (pl : Bool)
    (z : Vertex d) (a : Fin d → ℝ)
    (herror : dist (scaledSpanningVertex t z) a ≤ (1/128:ℝ))
    (hlo : -(1/3:ℝ) ≤ realSpanningHeight f a)
    (hwidth : ∀ j, j ≠ f.1 → |a j| ≤ (1/3:ℝ))
    (hbranch : (3/8:ℝ) ≤ realSpanningHeight f a → ∀ j, j ≠ f.1 →
      (9/64:ℝ) ≤ (if pl then a j else -a j) ∧ (if pl then a j else -a j) ≤ 15/64) :
    let N := (t - 1) / 2
    -((N:ℕ):ℤ) ≤ faceHeight f z ∧
      (∀ j, j ≠ f.1 → |z j| ≤ (N:ℤ)) ∧
      ((N:ℤ) < faceHeight f z → ∀ j, j ≠ f.1 → splitRange t pl (z j)) := by
  intro N
  have htpos : (0:ℝ) < t := by exact_mod_cast (Nat.zero_lt_one.trans_le ht)
  have hscale : realSpanningHeight f (scaledSpanningVertex t z) = (faceHeight f z:ℝ)/(t:ℝ) := by
    obtain ⟨i,s⟩ := f
    cases s <;> simp [realSpanningHeight,scaledSpanningVertex,faceHeight,neg_div]
  have hheight := spanning_embedding_coordinate_error herror f.1
  rw [← realSpanningHeight_sub_abs f, hscale] at hheight
  have hheight' := abs_le.mp hheight
  refine ⟨?_,?_,?_⟩
  · by_cases h : (faceHeight f z:ℝ) < (t:ℝ)/2
    · have h' := (lt_div_iff₀ htpos).mp
        (show -(1/2:ℝ) < (faceHeight f z:ℝ)/(t:ℝ) by linarith)
      exact ((halfSide_iff ht (faceHeight f z)).mpr ⟨by linarith, h⟩).1
    · have hh : 0 ≤ faceHeight f z := by
        exact_mod_cast (show (0:ℝ) ≤ (faceHeight f z:ℝ) by linarith)
      exact (neg_nonpos.mpr (Nat.cast_nonneg N)).trans hh
  · intro j hj
    have he := abs_le.mp (spanning_embedding_coordinate_error herror j)
    have hw := abs_le.mp (hwidth j hj)
    change -(1/128:ℝ) ≤ (z j:ℝ)/(t:ℝ)-a j ∧ (z j:ℝ)/(t:ℝ)-a j ≤ 1/128 at he
    apply abs_le.mpr
    apply (halfSide_iff ht (z j)).mpr
    constructor
    · have h := (lt_div_iff₀ htpos).mp (show -(1/2:ℝ) < (z j:ℝ)/(t:ℝ) by linarith)
      linarith
    · have h := (div_lt_iff₀ htpos).mp (show (z j:ℝ)/(t:ℝ) < 1/2 by linarith)
      linarith
  · intro hz j hj
    have hz' : (t:ℝ)/2 ≤ (faceHeight f z:ℝ) := by
      by_contra! h
      have hpos : (0:ℝ) ≤ (faceHeight f z:ℝ) := by
        exact_mod_cast (show 0 ≤ faceHeight f z by omega)
      exact (not_le_of_gt hz) ((halfSide_iff ht (faceHeight f z)).mpr ⟨by linarith,h⟩).2
    have hh : (1/2:ℝ) ≤ (faceHeight f z:ℝ)/(t:ℝ) := (le_div_iff₀ htpos).mpr (by linarith)
    have hb := hbranch (by linarith) j hj
    have he := abs_le.mp (spanning_embedding_coordinate_error herror j)
    change -(1/128:ℝ) ≤ (z j:ℝ)/(t:ℝ)-a j ∧ (z j:ℝ)/(t:ℝ)-a j ≤ 1/128 at he
    cases pl
    · change (9/64:ℝ) ≤ -a j ∧ -a j ≤ 15/64 at hb
      have hl := (lt_div_iff₀ htpos).mp (show -(1/4:ℝ) < (z j:ℝ)/(t:ℝ) by linarith)
      have hu := (div_lt_iff₀ htpos).mp (show (z j:ℝ)/(t:ℝ) < -(1/8:ℝ) by linarith)
      exact ⟨by linarith, by linarith⟩
    · change (9/64:ℝ) ≤ a j ∧ a j ≤ 15/64 at hb
      have hl := (lt_div_iff₀ htpos).mp (show (1/8:ℝ) < (z j:ℝ)/(t:ℝ) by linarith)
      have hu := (div_lt_iff₀ htpos).mp (show (z j:ℝ)/(t:ℝ) < (1/4:ℝ) by linarith)
      exact ⟨by linarith, by linarith⟩

/-- The actual split crossing follows from a pointed chemical
correspondence and a limiting geodesic with the split-channel margins. -/
theorem chemical_correspondence_crossSplit {d t : ℕ} {T : Type*} [PseudoMetricSpace T]
    (ht : 1 ≤ t) (f : Fin d × Bool) (pl : Bool) (ω : Configuration d) {o v : Vertex d}
    (ho : o ∈ typicalCube t (0 : Vertex d))
    (c : ℝ) (hc : 0 ≤ c) (R : Vertex d → T → Prop) (ε η : ℝ)
    (hη : 0 ≤ η) (hsmall : ε+η ≤ (1/128:ℝ))
    (hR : ∀ x a, R x a → (openGraph ω).Reachable o x)
    (hcover : ∀ x, (openGraph ω).Reachable o x → ∃ a, R x a)
    (hdist : ∀ x a x' a', R x a → R x' a' →
      |c*((openGraph ω).dist x x':ℝ)-dist a a'| ≤ ε)
    (treeProjection : ∀ r y b : T, ∃ a : T,
      dist r a+dist a y = dist r y ∧ 2*dist b a = dist r b+dist b y-dist r y)
    (Φ : T → (Fin d → ℝ))
    (hembed : ∀ x a, R x a → dist (scaledSpanningVertex t x) (Φ a) ≤ ε)
    (hmodulus : ∀ a b : T, dist a b ≤ 3*ε/2 → dist (Φ a) (Φ b) ≤ η)
    {r y : T} (hor : R o r) (hvy : R v y)
    (hchannel : ∀ a : T, dist r a+dist a y = dist r y →
      (-(1/3:ℝ) ≤ realSpanningHeight f (Φ a)) ∧
      (∀ j, j ≠ f.1 → |Φ a j| ≤ (1/3:ℝ)) ∧
      ((3/8:ℝ) ≤ realSpanningHeight f (Φ a) → ∀ j, j ≠ f.1 →
        (9/64:ℝ) ≤ (if pl then Φ a j else -Φ a j) ∧
        (if pl then Φ a j else -Φ a j) ≤ 15/64))
    (hend : (7/4:ℝ) ≤ realSpanningHeight f (Φ y)) :
    ω ∈ crossSplit t f pl t o := by
  obtain ⟨w,hnear⟩ := chemical_correspondence_geodesic_near ω c hc R ε η hR hcover hdist
    treeProjection Φ hembed hmodulus hor hvy
  have hcoord (z : Vertex d) (hz : z ∈ w.support) :
      let N := (t - 1) / 2
      -((N:ℕ):ℤ) ≤ faceHeight f z ∧
        (∀ j, j ≠ f.1 → |z j| ≤ (N:ℤ)) ∧
        ((N:ℤ) < faceHeight f z → ∀ j, j ≠ f.1 → splitRange t pl (z j)) := by
    obtain ⟨a,ha,he⟩ := hnear z hz
    obtain ⟨h₁,h₂,h₃⟩ := hchannel a ha
    exact split_channel_coordinates ht f pl z (Φ a) (he.trans hsmall) h₁ h₂ h₃
  refine crossSplit_of_walk_channel w t t f pl ht (Nat.zero_lt_one.trans_le ht) ho ?_
    (fun z hz => (hcoord z hz).1) (fun z hz => (hcoord z hz).2.1) (fun z hz => (hcoord z hz).2.2)
  have htpos : 0 < (t:ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le ht)
  have hscale : realSpanningHeight f (scaledSpanningVertex t v) = (faceHeight f v:ℝ)/(t:ℝ) := by
    obtain ⟨i,s⟩ := f
    cases s <;> simp [realSpanningHeight,scaledSpanningVertex,faceHeight,neg_div]
  have he := spanning_embedding_coordinate_error (hembed v y hvy) f.1
  rw [← realSpanningHeight_sub_abs f, hscale] at he
  have hlo := (abs_le.mp he).1
  have hreach := (le_div_iff₀ htpos).mp
    (show (3/2:ℝ) ≤ (faceHeight f v:ℝ)/(t:ℝ) by linarith)
  have hN : 2 * (((t-1)/2:ℕ):ℝ) ≤ (t:ℝ) := by
    exact_mod_cast (show 2*((t-1)/2) ≤ t by omega)
  exact_mod_cast (show (((t-1)/2:ℕ):ℝ) + (t:ℝ) ≤ (faceHeight f v:ℝ) by linarith)

end NearCritical.Section10
