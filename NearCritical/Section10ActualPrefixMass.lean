module

public import NearCritical.Section10NormalizedOccupation
public import NearCritical.Section10Survivor
public import NearCritical.Section10MergeSchedule

/-! Freshness, normalization and local blocks for the actual nest rule. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

theorem leftBlock_subset_mergedTraceBlocks {d : ℕ} (B B' : ℕ → Finset (LBond d))
    (s : List PairMove) (t t' : ℕ) (j : ℕ) (hj : j < leftCount s) :
    B (t+j) ⊆ mergedTraceBlocks B B' s t t' := by
  induction s generalizing t t' j with
  | nil => simp [leftCount] at hj
  | cons m s ih =>
    cases m
    · change B (t+j) ⊆ B t ∪ mergedTraceBlocks B B' s (t+1) t'
      cases j with
      | zero => simpa only [Nat.add_zero] using
          (Finset.subset_union_left : B t ⊆ B t ∪ mergedTraceBlocks B B' s (t+1) t')
      | succ j =>
        have hh := ih (t+1) t' j (Nat.lt_of_succ_lt_succ hj)
        have ht : B (t+(j+1)) ⊆ mergedTraceBlocks B B' s (t+1) t' := by
          simpa only [Nat.add_assoc,Nat.add_comm 1] using hh
        exact ht.trans Finset.subset_union_right
    · exact (ih t (t'+1) j hj).trans Finset.subset_union_right
    · change B (t+j) ⊆ (B t ∪ B' t') ∪ mergedTraceBlocks B B' s (t+1) (t'+1)
      cases j with
      | zero =>
        rw [Nat.add_zero]
        exact (Finset.subset_union_left : B t ⊆ B t ∪ B' t').trans Finset.subset_union_left
      | succ j =>
        have hh := ih (t+1) (t'+1) j (Nat.lt_of_succ_lt_succ hj)
        have ht : B (t+(j+1)) ⊆ mergedTraceBlocks B B' s (t+1) (t'+1) := by
          simpa only [Nat.add_assoc,Nat.add_comm 1] using hh
        exact ht.trans Finset.subset_union_right

namespace NestRule

variable {D M d : ℕ} {X Φ : Type} [Fintype X] [Fintype Φ]
  {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ X Φ)

theorem kernel_row_integral_eq_one (hρ : 0 < ρ) (γ : SourceRoute D M) (G : Φ) (j : ℕ) (x : X) :
    (∫ z, ∑ y, R.kernel γ G j x y z ∂((percolation d p).prod (percolation d q))) = 1 :=
  stepKernel_integral_eq_one p q _ _ _ (R.ho γ G j x) ((inv_pos.mpr hρ).trans_le (R.hs γ G j x))

theorem kernel_pair_row_integral_le (hρ : 0 < ρ) (γ γ' : SourceRoute D M)
    (G : Φ) (j j' : ℕ) (x x' : X) :
    (∫ z, ∑ y : X × X, R.kernel γ G j x y.1 z * R.kernel γ' G j' x' y.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ρ := by
  have hp := (inv_pos.mpr hρ).trans_le (R.hs γ G j x)
  have hp' := (inv_pos.mpr hρ).trans_le (R.hs γ' G j' x')
  exact (stepKernel_pair_integral_le p q _ _ _ _ _ _ (R.ho γ G j x) (R.ho γ' G j' x')
    hp hp').trans ((inv_le_comm₀ hp' hρ).mpr (R.hs γ' G j' x'))

/-- Every joint route schedule is fresh at a fixed reveal. -/
theorem route_pair_fresh (hM : 1 ≤ M) (γ γ' : SourceRoute D M) (G : Φ)
    (n n' t t' : ℕ) :
    PairFresh (fun i => R.Bl G (routeLab M γ.position i))
      (fun i => R.Bl G (routeLab M γ'.position i))
      (mergeSched RouteLabel.rank (routeLab M γ.position) (routeLab M γ'.position) n n' t t')
      t t' (R.S G) :=
  mergeSched_fresh RouteLabel.rank (routeLab M γ.position) (routeLab M γ'.position)
    (R.Bl G) (R.hBl G) (routeLab_strictMono hM _) (routeLab_strictMono hM _)
    (n+n') n n' t t' (R.S G) le_rfl (fun i _ _ => R.hS G _) (fun i _ _ => R.hS G _)

/-- The actual normalized history has total mass at most one before
inserting any occupation or collision marks. -/
theorem unmarked_prefix_mass_le_one (hρ : 0 < ρ) (γ γ' : SourceRoute D M) (G : Φ)
    (s : List PairMove) (x : X × X) :
    let B (δ : SourceRoute D M) j := R.Bl G (routeLab M δ.position j)
    PairFresh (B γ) (B γ') s 0 0 (R.S G) →
    markedPrefixMass p q (R.kernel γ G) (R.kernel γ' G) s 0 0 x (fun _ _ => 1) /
      ρ ^ sharedCount s ≤ 1 := by
  intro B hFresh
  have hloc (δ : SourceRoute D M) (j : ℕ) (u v : X) : IsLocal (B δ j) (R.kernel δ G j u v) :=
    stepKernel_isLocal _ _ _ _ v
  have hnon (δ : SourceRoute D M) (j : ℕ) (u v : X) (z : Configuration d × Configuration d) :
      0 ≤ R.kernel δ G j u v z :=
    stepKernel_nonneg _ _ _ ((inv_pos.mpr hρ).trans_le (R.hs δ G j u)).le v z
  have h := markedPrefixMass_normalized_suffix_le p q (B γ) (B γ')
    (R.kernel γ G) (R.kernel γ' G) (hloc γ) (hloc γ') (hnon γ) (hnon γ') hρ
    (fun t x => (R.kernel_row_integral_eq_one hρ γ G t x).le)
    (fun t x => (R.kernel_row_integral_eq_one hρ γ' G t x).le)
    (fun t t' x x' => R.kernel_pair_row_integral_le hρ γ γ' G t t' x x')
    [] s 0 0 x (R.S G) hFresh (fun _ _ => 1)
    (fun _ => isLocal_const _ 1) (fun _ _ => zero_le_one)
  have hempty : markedPrefixMass p q (R.kernel γ G) (R.kernel γ' G) [] 0 0 x (fun _ _ => 1) = 1 := by
    unfold markedPrefixMass
    change (∫ _z, ∑ _h : PUnit, (1:ℝ) * 1 ∂((percolation d p).prod (percolation d q))) = 1
    simp
  simpa only [List.nil_append, sharedCount, pow_zero, div_one, hempty] using h

end NestRule
end NearCritical.Section10
