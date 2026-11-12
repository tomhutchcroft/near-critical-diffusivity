module
public import NearCritical.Section9PhysicalBond
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The source shared-physical-pivot count, allowing reversal aliases. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

private theorem physical_overlap_fiber {d : ℕ}
    (S : Finset (Vertex d × Vertex d)) (bond : (Vertex d × Vertex d) → Bond d)
    (hends : ∀ e ∈ S, s((bond e).1,bondTip (bond e)) = s(e.1,e.2)) (b : Bond d) :
    S.filter (fun e => bond e = b) =
      ({(b.1,bondTip b),(bondTip b,b.1)} : Finset (Vertex d × Vertex d)).filter (fun e => e ∈ S) := by
  ext e
  simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨he,hb⟩
    have hh := hends e he
    rw [hb] at hh
    rcases Sym2.eq_iff.mp hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact ⟨Or.inl (Prod.ext h₁.symm h₂.symm),he⟩
    · exact ⟨Or.inr (Prod.ext h₂.symm h₁.symm),he⟩
  · rintro ⟨h | h,he⟩
    · subst e
      exact ⟨he,section9_bond_endpoints_injective (hends _ he)⟩
    · subst e
      exact ⟨he,section9_bond_endpoints_injective ((hends _ he).trans Sym2.eq_swap)⟩

private theorem physical_overlap_image_iff {d : ℕ}
    (S : Finset (Vertex d × Vertex d)) (bond : (Vertex d × Vertex d) → Bond d)
    (hends : ∀ e ∈ S, s((bond e).1,bondTip (bond e)) = s(e.1,e.2)) (b : Bond d) :
    b ∈ S.image bond ↔ (b.1,bondTip b) ∈ S ∨ (bondTip b,b.1) ∈ S := by
  rw [← Finset.fiber_nonempty_iff_mem_image,physical_overlap_fiber S bond hends b]
  by_cases hp : (b.1,bondTip b) ∈ S <;> by_cases hm : (bondTip b,b.1) ∈ S <;>
    simp [Finset.filter_insert,Finset.filter_singleton,hp,hm]

private theorem physical_overlap_card {d : ℕ}
    (S : Finset (Vertex d × Vertex d)) (H : Finset (Bond d))
    (bond : (Vertex d × Vertex d) → Bond d)
    (hends : ∀ e ∈ S, s((bond e).1,bondTip (bond e)) = s(e.1,e.2))
    (hH : ∀ e ∈ S, bond e ∈ H) :
    (S.card : ℝ) = ∑ b ∈ H,
      ((if (b.1,bondTip b) ∈ S then (1 : ℝ) else 0)+
       (if (bondTip b,b.1) ∈ S then (1 : ℝ) else 0)) := by
  have hc := Finset.card_eq_sum_card_fiberwise (f := bond) hH
  rw [hc,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [physical_overlap_fiber S bond hends b]
  have hne : (b.1,bondTip b) ≠ (bondTip b,b.1) := by
    intro h
    exact bondTip_ne_base b (congrArg Prod.fst h).symm
  by_cases hp : (b.1,bondTip b) ∈ S <;> by_cases hm : (bondTip b,b.1) ∈ S <;>
    simp [Finset.filter_insert,Finset.filter_singleton,hp,hm,hne] <;> ring

private theorem physical_overlap_indicator_card {α : Type*} [DecidableEq α]
    (H S : Finset α) (hsub : S ⊆ H) :
    (S.card : ℝ) = ∑ b ∈ H, if b ∈ S then (1 : ℝ) else 0 := by
  have hf : H.filter (fun b => b ∈ S) = S := by
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
  rw [Finset.sum_boole,hf]

private theorem physical_overlap_ordered_pairs {ι : Type*} [DecidableEq ι]
    (I S : Finset ι) (hSI : S ⊆ I) :
    (∑ i ∈ I, ∑ j ∈ I.erase i, if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) =
      (S.card : ℝ)^2-(S.card : ℝ) := by
  have hrow (i : ι) :
      (∑ j ∈ I.erase i, if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) =
        if i ∈ S then (S.card : ℝ)-1 else 0 := by
    by_cases hi : i ∈ S
    · have hf : (I.erase i).filter (fun j => j ∈ S) = S.erase i := by
        ext j
        simp only [Finset.mem_filter,Finset.mem_erase]
        constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · exact fun h => ⟨⟨h.1,hSI h.2⟩,h.2⟩
      simp only [hi,true_and,if_true]
      rw [Finset.sum_boole,hf,Finset.card_erase_of_mem hi,
        Nat.cast_sub (show 1 ≤ S.card from Finset.one_le_card.mpr ⟨i,hi⟩),Nat.cast_one]
    · simp only [hi,false_and,if_false,Finset.sum_const_zero]
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  have hf : I.filter (fun i => i ∈ S) = S := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hSI h,h⟩⟩
  rw [hf,Finset.sum_const,nsmul_eq_mul]
  ring

private theorem physical_overlap_scalar {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    ((S ∪ T).card : ℝ)^2-((S ∪ T).card : ℝ) ≤
      2*((S.card : ℝ)^2-(S.card : ℝ)+((T.card : ℝ)^2-(T.card : ℝ)))+
        ((S.card : ℝ)+(T.card : ℝ)) := by
  by_cases hu : (S ∪ T).Nonempty
  · have hk : (1 : ℝ) ≤ (S ∪ T).card := by exact_mod_cast Finset.one_le_card.mpr hu
    have hle : ((S ∪ T).card : ℝ) ≤ (S.card : ℝ)+(T.card : ℝ) := by
      exact_mod_cast Finset.card_union_le S T
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ (S.card : ℝ)+(T.card : ℝ)+((S ∪ T).card : ℝ)-1 by linarith)
    nlinarith only [hp,sq_nonneg ((S.card : ℝ)-(T.card : ℝ))]
  · have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => hu ⟨i,Finset.mem_union_left T hi⟩)
    have hT : T = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => hu ⟨i,Finset.mem_union_right S hi⟩)
    simp only [hS,hT,Finset.union_self,Finset.card_empty,Nat.cast_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),
      sub_zero,add_zero,mul_zero,le_refl]

private theorem physical_overlap_move_sum {ι β : Type*} [DecidableEq ι]
    (I : Finset ι) (H : Finset β) (f : ι → ι → β → ℝ) :
    (∑ i ∈ I, ∑ j ∈ I.erase i, ∑ b ∈ H, f i j b) =
      ∑ b ∈ H, ∑ i ∈ I, ∑ j ∈ I.erase i, f i j b := by
  calc
    _ = ∑ i ∈ I, ∑ b ∈ H, ∑ j ∈ I.erase i, f i j b :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- Physical shared-target overlap is controlled by SAME-oriented overlap
plus the oriented first moment. Reversed uses of one physical bond are allowed.
All target pairs are ordered and distinct; no probability or target disjointness
hypothesis is required. -/
theorem section9_shared_physical_pivot_overlap_le {d : ℕ} {ι : Type*}
    (I : Finset ι) (P : ι → Finset (Vertex d × Vertex d))
    (bond : (Vertex d × Vertex d) → Bond d)
    (hends : ∀ i ∈ I, ∀ e ∈ P i, s((bond e).1,bondTip (bond e)) = s(e.1,e.2)) :
    (∑ i ∈ I, ∑ j ∈ I.erase i,
      (((P i).image bond ∩ (P j).image bond).card : ℝ)) ≤
      2*(∑ i ∈ I, ∑ j ∈ I.erase i, ((P i ∩ P j).card : ℝ))+
        ∑ i ∈ I, ((P i).card : ℝ) := by
  let H := (I.biUnion P).image bond
  let S := fun b : Bond d => I.filter (fun i => (b.1,bondTip b) ∈ P i)
  let T := fun b : Bond d => I.filter (fun i => (bondTip b,b.1) ∈ P i)
  have hH (i : ι) (hi : i ∈ I) (e) (he : e ∈ P i) : bond e ∈ H :=
    Finset.mem_image.mpr ⟨e,Finset.mem_biUnion.mpr ⟨i,hi,he⟩,rfl⟩
  have hS (b : Bond d) : S b ⊆ I := Finset.filter_subset _ _
  have hT (b : Bond d) : T b ⊆ I := Finset.filter_subset _ _
  have hU (b : Bond d) : S b ∪ T b ⊆ I := Finset.union_subset (hS b) (hT b)
  have hphysical : (∑ i ∈ I, ∑ j ∈ I.erase i,
      (((P i).image bond ∩ (P j).image bond).card : ℝ)) =
      ∑ b ∈ H, (((S b ∪ T b).card : ℝ)^2-((S b ∪ T b).card : ℝ)) := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ b ∈ H,
          if b ∈ (P i).image bond ∩ (P j).image bond then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j _
        apply physical_overlap_indicator_card
        intro b hb
        obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
        exact hH i hi e he
      _ = ∑ b ∈ H, ∑ i ∈ I, ∑ j ∈ I.erase i,
          if b ∈ (P i).image bond ∩ (P j).image bond then (1 : ℝ) else 0 :=
        physical_overlap_move_sum I H _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← physical_overlap_ordered_pairs I (S b ∪ T b) (hU b)]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hjI := (Finset.mem_erase.mp hj).2
        simp only [Finset.mem_inter,physical_overlap_image_iff (P i) bond (hends i hi) b,
          physical_overlap_image_iff (P j) bond (hends j hjI) b,S,T,Finset.mem_union,
          Finset.mem_filter,hi,hjI,true_and]
  have horiented : (∑ i ∈ I, ∑ j ∈ I.erase i, ((P i ∩ P j).card : ℝ)) =
      ∑ b ∈ H, (((S b).card : ℝ)^2-((S b).card : ℝ)+
        (((T b).card : ℝ)^2-((T b).card : ℝ))) := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ b ∈ H,
          ((if (b.1,bondTip b) ∈ P i ∩ P j then (1 : ℝ) else 0)+
           (if (bondTip b,b.1) ∈ P i ∩ P j then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j _
        exact physical_overlap_card (P i ∩ P j) H bond
          (fun e he => hends i hi e (Finset.mem_inter.mp he).1)
          (fun e he => hH i hi e (Finset.mem_inter.mp he).1)
      _ = ∑ b ∈ H, ∑ i ∈ I, ∑ j ∈ I.erase i,
          ((if (b.1,bondTip b) ∈ P i ∩ P j then (1 : ℝ) else 0)+
           (if (bondTip b,b.1) ∈ P i ∩ P j then (1 : ℝ) else 0)) :=
        physical_overlap_move_sum I H _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        simp_rw [Finset.sum_add_distrib]
        rw [← physical_overlap_ordered_pairs I (S b) (hS b),
          ← physical_overlap_ordered_pairs I (T b) (hT b)]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
          apply Finset.sum_congr rfl <;> intro j hj <;>
          simp only [Finset.mem_inter,S,T,Finset.mem_filter,hi,
            (Finset.mem_erase.mp hj).2,true_and]
  have hfirst : (∑ i ∈ I, ((P i).card : ℝ)) =
      ∑ b ∈ H, (((S b).card : ℝ)+((T b).card : ℝ)) := by
    calc
      _ = ∑ i ∈ I, ∑ b ∈ H,
          ((if (b.1,bondTip b) ∈ P i then (1 : ℝ) else 0)+
           (if (bondTip b,b.1) ∈ P i then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun i hi => physical_overlap_card (P i) H bond (hends i hi) (hH i hi))
      _ = ∑ b ∈ H, ∑ i ∈ I,
          ((if (b.1,bondTip b) ∈ P i then (1 : ℝ) else 0)+
           (if (bondTip b,b.1) ∈ P i then (1 : ℝ) else 0)) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [Finset.sum_add_distrib,Finset.sum_boole,S,T]
  rw [hphysical,horiented,hfirst,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun b _ => physical_overlap_scalar (S b) (T b))

end NearCritical
