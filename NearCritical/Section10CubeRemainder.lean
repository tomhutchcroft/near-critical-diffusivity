module

public import NearCritical.AnnealedSubadditivity
public import NearCritical.ConductivityUpperBound

/-! The remainder comparison needed for the Section10 affine-box limit.
Partition BASE SITES into one rectangle and singleton remainder cells, then
apply the existing full Dirichlet subadditivity. Enlarged supports may overlap;
no domain monotonicity or conductivity convergence is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

theorem latticeRectangle_singleton {d : ℕ} (x : Vertex d) :
    latticeRectangle x x = {x} := by
  ext y
  simp only [Finset.mem_singleton]
  constructor
  · intro hy
    funext k
    exact le_antisymm (mem_latticeRectangle.mp hy k).2 (mem_latticeRectangle.mp hy k).1
  · rintro rfl
    exact mem_latticeRectangle.mpr (fun k => ⟨le_rfl,le_rfl⟩)

/-- The actual mean on a finite base domain is bounded by its rectangular
interior mean and the affine competitor on each remaining singleton. -/
theorem annealedFull_rectangle_singleton_remainder {d : ℕ}
    (T : Finset (Vertex d)) (lo hi : Vertex d) (hvalid : ∀ k, lo k ≤ hi k)
    (hVT : latticeRectangle lo hi ⊆ T) (p : unitInterval) (i : Fin d) :
    annealedFull T i (p:ℝ) ≤
      ((latticeRectangle lo hi).card:ℝ)/(T.card:ℝ)*
        annealedFull (latticeRectangle lo hi) i (p:ℝ) +
      ((T \ latticeRectangle lo hi).card:ℝ)/(T.card:ℝ)*(p:ℝ) := by
  let V := latticeRectangle lo hi
  let R := T \ V
  let s : Finset (Option (Vertex d)) := insert none (R.image some)
  let lower : Option (Vertex d) → Vertex d := fun j => j.elim lo id
  let upper : Option (Vertex d) → Vertex d := fun j => j.elim hi id
  let U : Option (Vertex d) → Finset (Vertex d) := fun j => j.elim V (fun x => {x})
  have hsome (x : Vertex d) : some x ∈ s ↔ x ∈ R := by
    simp [s,Finset.mem_image]
  have hcell (j : Option (Vertex d)) : latticeRectangle (lower j) (upper j) = U j := by
    cases j with
    | none => rfl
    | some x => exact latticeRectangle_singleton x
  have hv : ∀ j ∈ s, ∀ k, lower j k ≤ upper j k := by
    intro j _ k
    cases j with
    | none => exact hvalid k
    | some x => exact le_rfl
  have hd : (s : Set (Option (Vertex d))).PairwiseDisjoint U := by
    intro j hj k hk hne
    cases j with
    | none =>
      cases k with
      | none => exact (hne rfl).elim
      | some y =>
        change Disjoint V {y}
        exact Finset.disjoint_singleton_right.mpr (Finset.mem_sdiff.mp ((hsome y).mp hk)).2
    | some x =>
      cases k with
      | none =>
        change Disjoint {x} V
        exact Finset.disjoint_singleton_left.mpr (Finset.mem_sdiff.mp ((hsome x).mp hj)).2
      | some y =>
        change Disjoint {x} {y}
        apply Finset.disjoint_singleton.mpr
        intro hxy
        exact hne (congrArg some hxy)
  have hcover : s.biUnion U = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hx
      cases j with
      | none => exact hVT hxj
      | some y =>
        have hyR := (hsome y).mp hj
        have hxy : x = y := Finset.mem_singleton.mp hxj
        rw [hxy]
        exact (Finset.mem_sdiff.mp hyR).1
    · intro hx
      by_cases hxV : x ∈ V
      · exact Finset.mem_biUnion.mpr ⟨none,by simp [s],hxV⟩
      · have hxR : x ∈ R := Finset.mem_sdiff.mpr ⟨hx,hxV⟩
        exact Finset.mem_biUnion.mpr ⟨some x,(hsome x).mpr hxR,by simp [U]⟩
  have hdrect : (s : Set (Option (Vertex d))).PairwiseDisjoint
      (fun j => latticeRectangle (lower j) (upper j)) := by
    simpa only [hcell] using hd
  have hb := annealedFull_rectangle_subadditivity s lower upper hv hdrect p i
  simp_rw [hcell] at hb
  rw [hcover] at hb
  have hnone : (none : Option (Vertex d)) ∉ R.image some := by simp
  change annealedFull T i (p:ℝ) ≤
    ∑ j ∈ insert none (R.image some), ((U j).card:ℝ)/(T.card:ℝ)*
      annealedFull (U j) i (p:ℝ) at hb
  rw [Finset.sum_insert hnone,
    Finset.sum_image (fun x _ y _ h => Option.some.inj h)] at hb
  dsimp only [U] at hb
  simp only [Option.elim_none,Option.elim_some,Finset.card_singleton,Nat.cast_one] at hb
  have hcoeff : 0 ≤ (1:ℝ)/(T.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hs : (∑ x ∈ R, (1:ℝ)/(T.card:ℝ)*annealedFull {x} i (p:ℝ)) ≤
      ∑ _x ∈ R, (1:ℝ)/(T.card:ℝ)*(p:ℝ) := by
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left
      (annealedFull_le_parameter {x} ⟨x,by simp⟩ i p) hcoeff
  calc
    _ ≤ ((V.card:ℝ)/(T.card:ℝ))*annealedFull V i (p:ℝ) +
        ∑ x ∈ R, (1:ℝ)/(T.card:ℝ)*annealedFull {x} i (p:ℝ) := hb
    _ ≤ ((V.card:ℝ)/(T.card:ℝ))*annealedFull V i (p:ℝ) +
        ∑ _x ∈ R, (1:ℝ)/(T.card:ℝ)*(p:ℝ) := add_le_add (le_refl _) hs
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; dsimp [V,R]; ring

/-- The remainder costs at most its fraction of actual base-site volume. -/
theorem annealedFull_rectangle_remainder_fraction {d : ℕ}
    (T : Finset (Vertex d)) (lo hi : Vertex d) (hvalid : ∀ k, lo k ≤ hi k)
    (hVT : latticeRectangle lo hi ⊆ T) (p : unitInterval) (i : Fin d) :
    annealedFull T i (p:ℝ) ≤ annealedFull (latticeRectangle lo hi) i (p:ℝ) +
      ((T \ latticeRectangle lo hi).card:ℝ)/(T.card:ℝ) := by
  have hT : T.Nonempty := ⟨lo,hVT (mem_latticeRectangle.mpr (fun k => ⟨le_rfl,hvalid k⟩))⟩
  have hTp : 0 < (T.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
  have hcard : ((latticeRectangle lo hi).card:ℝ) ≤ (T.card:ℝ) := by
    exact_mod_cast Finset.card_le_card hVT
  have hfrac : ((latticeRectangle lo hi).card:ℝ)/(T.card:ℝ) ≤ 1 :=
    (div_le_one hTp).mpr hcard
  have ha := annealedFull_nonneg (latticeRectangle lo hi) i p.2.1 p.2.2
  have hr : 0 ≤ ((T \ latticeRectangle lo hi).card:ℝ)/(T.card:ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hTp.le
  have hb := annealedFull_rectangle_singleton_remainder T lo hi hvalid hVT p i
  refine hb.trans ?_
  have hleft := mul_le_mul_of_nonneg_right hfrac ha
  have hright := mul_le_mul_of_nonneg_left p.2.2 hr
  simpa only [one_mul,mul_one] using add_le_add hleft hright

end NearCritical.Section10
