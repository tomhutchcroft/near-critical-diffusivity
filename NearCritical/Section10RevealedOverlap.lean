module

public import NearCritical.Section10PairOverlap
public import NearCritical.Section10Trajectories

/-! `eq.nw.pair.overlap` conditional on a finite-valued reveal.

`revealed_pair_entanglement_le`: on each atom `F` of the reveal the pair chain
has its own blocks and kernels `K F = a F + b F`, site marks `c F`, step bounds
`rho F`, `delta F`, and start state. If on every atom the one-step estimates of
`pair_entanglement_le` hold, then for every weight `w >= 0` of the reveal

  `E[w(reveal) * (2 #tube + #site, weighted)] <= E[w(reveal) * bound(reveal)]`,

with `bound F = prod rho F * ((2/(1-theta)) (a_0 + sum delta F) + sum delta F)`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- The bound of `pair_entanglement_le` at the start of the chain. -/
def entanglementBound (ρ δ : ℕ → ℝ) (θ a₀ : ℝ) (m : ℕ) : ℝ :=
  stepProd ρ m 0 * (2 * ((1 - θ)⁻¹ * a₀ + (1 - θ)⁻¹ * stepSum δ m 0) + stepSum δ m 0)

theorem revealed_pair_entanglement_le {d : ℕ} {S Φ : Type*} [Fintype S] [Fintype Φ]
    (p q : unitInterval) (ρr : Configuration d × Configuration d → Φ)
    (Sx : Φ → Finset (LBond d))
    (hρr : ∀ F, IsLocal (Sx F) (fun z => if ρr z = F then (1:ℝ) else 0))
    (B : Φ → ℕ → Finset (LBond d)) (hB : ∀ F i j, i ≠ j → Disjoint (B F i) (B F j))
    (hSB : ∀ F j, Disjoint (Sx F) (B F j))
    (K a b c : Φ → ℕ → S → S → Configuration d × Configuration d → ℝ)
    (hK : ∀ F t x y, IsLocal (B F t) (K F t x y)) (ha : ∀ F t x y, IsLocal (B F t) (a F t x y))
    (hb : ∀ F t x y, IsLocal (B F t) (b F t x y)) (hc : ∀ F t x y, IsLocal (B F t) (c F t x y))
    (ha0 : ∀ F t x y z, 0 ≤ a F t x y z) (hb0 : ∀ F t x y z, 0 ≤ b F t x y z)
    (hc0 : ∀ F t x y z, 0 ≤ c F t x y z)
    (hKab : ∀ F t x y z, K F t x y z = a F t x y z + b F t x y z)
    (ρ δ : Φ → ℕ → ℝ) (hρ : ∀ F t, 1 ≤ ρ F t) (hδ : ∀ F t, 0 ≤ δ F t) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hrow : ∀ F t x,
      ∑ y, (∫ z, K F t x y z ∂((percolation d p).prod (percolation d q))) ≤ ρ F t)
    (φ : Φ → ℕ → S → ℝ) (hφ0 : ∀ F t x, 0 ≤ φ F t x)
    (hpersist : ∀ F t x, ∑ y, (∫ z, a F t x y z ∂((percolation d p).prod (percolation d q))) * φ F (t+1) y ≤
      θ * ∑ y, ∫ z, a F t x y z ∂((percolation d p).prod (percolation d q)))
    (henter : ∀ F t x, ∑ y, (∫ z, b F t x y z ∂((percolation d p).prod (percolation d q))) * φ F (t+1) y ≤
      φ F t x - (∑ y, ∫ z, a F t x y z ∂((percolation d p).prod (percolation d q))) + δ F t)
    (hsite : ∀ F t x,
      ∑ y, (∫ z, c F t x y z ∂((percolation d p).prod (percolation d q))) ≤ δ F t)
    (w : Φ → ℝ) (hw : ∀ F, 0 ≤ w F) (m : ℕ) (x₀ : Φ → S) :
    (∫ z, w (ρr z) * (2 * markedValue (K (ρr z)) (a (ρr z)) m 0 (x₀ (ρr z)) z +
        markedValue (K (ρr z)) (c (ρr z)) m 0 (x₀ (ρr z)) z)
      ∂((percolation d p).prod (percolation d q))) ≤
      ∫ z, w (ρr z) * entanglementBound (ρ (ρr z)) (δ (ρr z)) θ
          (φ (ρr z) 0 (x₀ (ρr z)))
          m
        ∂((percolation d p).prod (percolation d q)) := by
  have hatom : ∀ (f : Φ → ℝ) (z : Configuration d × Configuration d),
      f (ρr z) = ∑ F, (if ρr z = F then (1:ℝ) else 0) * f F := by
    intro f z
    rw [Finset.sum_eq_single (ρr z)]
    · rw [if_pos rfl, one_mul]
    · intro F _ hF
      rw [if_neg (Ne.symm hF), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hloc : ∀ F, IsLocal (Sx F) (fun z => (if ρr z = F then (1:ℝ) else 0) * w F) :=
    fun F => (hρr F).mul (isLocal_const (Sx F) (w F))
  have hnn : ∀ F z, 0 ≤ (if ρr z = F then (1:ℝ) else 0) * w F := by
    intro F z
    refine mul_nonneg ?_ (hw F)
    split_ifs <;> norm_num
  obtain ⟨bd, hbd⟩ : ∃ bd : Φ → ℝ, bd = fun F => entanglementBound (ρ F) (δ F) θ
      (φ F 0 (x₀ F)) m := ⟨_, rfl⟩
  have hterm : ∀ F, (∫ z, ((if ρr z = F then (1:ℝ) else 0) * w F) *
      (2 * markedValue (K F) (a F) m 0 (x₀ F) z + markedValue (K F) (c F) m 0 (x₀ F) z)
        ∂((percolation d p).prod (percolation d q))) ≤
      (∫ z, (if ρr z = F then (1:ℝ) else 0) * w F
        ∂((percolation d p).prod (percolation d q))) * bd F := by
    intro F
    rw [hbd]
    exact pair_entanglement_le p q (B F) (hB F) (K F) (a F) (b F) (c F) (hK F) (ha F) (hb F)
      (hc F) (ha0 F) (hb0 F) (hc0 F) (hKab F) (hρ F) (hδ F) hθ0 hθ1 (hrow F) (φ F) (hφ0 F) (hpersist F)
      (henter F) (hsite F) m 0 (x₀ F) (Sx F) _ (hloc F) (hnn F)
      (fun j _ => by rw [Nat.zero_add]; exact hSB F j)
  have hint : ∀ F, Integrable (fun z => ((if ρr z = F then (1:ℝ) else 0) * w F) *
      (2 * markedValue (K F) (a F) m 0 (x₀ F) z + markedValue (K F) (c F) m 0 (x₀ F) z))
      ((percolation d p).prod (percolation d q)) := by
    intro F
    have h1 := markedValue_isLoc (B F) (K F) (a F) (hK F) (ha F) m 0 (x₀ F)
    have h2 := markedValue_isLoc (B F) (K F) (c F) (hK F) (hc F) m 0 (x₀ F)
    have h3 : IsLoc (fun z => 2 * markedValue (K F) (a F) m 0 (x₀ F) z +
        markedValue (K F) (c F) m 0 (x₀ F) z) := by
      have := isLoc_sum (Y := Bool) (F := fun bo z =>
        if bo then 2 * markedValue (K F) (a F) m 0 (x₀ F) z
        else markedValue (K F) (c F) m 0 (x₀ F) z) (fun bo => by
          cases bo
          · simpa using h2
          · simpa using (isLoc_const 2).mul h1)
      simpa [Fintype.sum_bool] using this
    exact (IsLoc.mul ⟨_, hloc F⟩ h3).integrable p q
  have hint2 : ∀ F, Integrable (fun z => ((if ρr z = F then (1:ℝ) else 0) * w F) * bd F)
      ((percolation d p).prod (percolation d q)) :=
    fun F => ((hloc F).mul (isLocal_const (Sx F) _)).integrable p q
  calc (∫ z, w (ρr z) * (2 * markedValue (K (ρr z)) (a (ρr z)) m 0 (x₀ (ρr z)) z +
        markedValue (K (ρr z)) (c (ρr z)) m 0 (x₀ (ρr z)) z)
        ∂((percolation d p).prod (percolation d q)))
      = ∫ z, ∑ F, ((if ρr z = F then (1:ℝ) else 0) * w F) *
          (2 * markedValue (K F) (a F) m 0 (x₀ F) z + markedValue (K F) (c F) m 0 (x₀ F) z)
          ∂((percolation d p).prod (percolation d q)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        have h := hatom (fun F => w F * (2 * markedValue (K F) (a F) m 0 (x₀ F) z +
          markedValue (K F) (c F) m 0 (x₀ F) z)) z
        refine h.trans ?_
        exact Finset.sum_congr rfl (fun F _ => (mul_assoc _ _ _).symm)
    _ = ∑ F, ∫ z, ((if ρr z = F then (1:ℝ) else 0) * w F) *
          (2 * markedValue (K F) (a F) m 0 (x₀ F) z + markedValue (K F) (c F) m 0 (x₀ F) z)
          ∂((percolation d p).prod (percolation d q)) :=
        integral_finsetSum _ (fun F _ => hint F)
    _ ≤ ∑ F, (∫ z, (if ρr z = F then (1:ℝ) else 0) * w F
          ∂((percolation d p).prod (percolation d q))) * bd F :=
        Finset.sum_le_sum (fun F _ => hterm F)
    _ = ∑ F, ∫ z, ((if ρr z = F then (1:ℝ) else 0) * w F) * bd F
          ∂((percolation d p).prod (percolation d q)) :=
        Finset.sum_congr rfl (fun F _ => (integral_mul_const (bd F) _).symm)
    _ = ∫ z, ∑ F, ((if ρr z = F then (1:ℝ) else 0) * w F) * bd F
          ∂((percolation d p).prod (percolation d q)) :=
        (integral_finsetSum _ (fun F _ => hint2 F)).symm
    _ = _ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        have h := hatom (fun F => w F * bd F) z
        rw [hbd] at h ⊢
        refine Eq.trans ?_ h.symm
        exact Finset.sum_congr rfl (fun F _ => mul_assoc _ _ _)

end NearCritical.Section10
