module

public import NearCritical.Section10RevealedOverlap
public import NearCritical.Section10OverlapEnergy

/-! The flow of `prop.nw.main` and its energy, pointwise in the configuration.

Every pair (route `γ`, trajectory `f`) is an individual chain with weight
`mu γ * (omega_γ * trajWeight)`; the total weight is `W`. Each chain carries a
unit flow `theta (γ, f)` supported on its path `P (γ, f)`.

* `trajWeight_pair`, `sum_pair_traj`: a pair of trajectories is a trajectory of
  the pair chain, with the product weight.
* `flow_energy_le_marked`: if `W >= 1/2`, the paths consist of open edges, and
  the number of common edges of two chains of positive weight is at most
  `Pb` times the number of marked steps of the pair (`lem.nw.overlap`), then

  `energy(normalised flow) <= 4 Pb sum_{γ,γ'} mu mu' omega omega' * markedValue(pair)`.

This is the display after `eq.nw.flow` in the proof of `prop.nw.main` (5784).
Taking expectations and applying `revealed_pair_entanglement_le` is the next
step; the flows, paths and the overlap lemma for the lattice rule are still to
be supplied.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open NearCritical.Network
open scoped Classical BigOperators

/-- A pair of trajectories as a trajectory of the pair chain. -/
def zipTraj {X X' : Type*} {m : ℕ} (f : Fin m → X) (f' : Fin m → X') : Fin m → X × X' :=
  fun i => (f i, f' i)

theorem trajWeight_pair {d : ℕ} {X X' : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ) :
    ∀ (m t : ℕ) (x : X) (x' : X') (f : Fin m → X) (f' : Fin m → X')
      (z : Configuration d × Configuration d),
      trajWeight (pairKernel k k') m t (x, x') (zipTraj f f') z =
        trajWeight k m t x f z * trajWeight k' m t x' f' z := by
  intro m
  induction m with
  | zero =>
    intro t x x' f f' z
    simp [trajWeight]
  | succ m ih =>
    intro t x x' f f' z
    have htail : Fin.tail (zipTraj f f') = zipTraj (Fin.tail f) (Fin.tail f') := rfl
    simp only [trajWeight, htail]
    have h0 : zipTraj f f' 0 = (f 0, f' 0) := rfl
    rw [h0, ih (t+1) (f 0) (f' 0) (Fin.tail f) (Fin.tail f') z]
    simp only [pairKernel]
    ring

/-- Pairs of trajectories are trajectories of pairs. -/
def zipEquiv (X X' : Type*) (m : ℕ) : (Fin m → X) × (Fin m → X') ≃ (Fin m → X × X') where
  toFun p := zipTraj p.1 p.2
  invFun F := (fun i => (F i).1, fun i => (F i).2)
  left_inv p := rfl
  right_inv F := rfl

lemma sum_pair_traj {X X' : Type*} [Fintype X] [Fintype X'] (m : ℕ)
    (Φ : (Fin m → X × X') → ℝ) :
    (∑ F : Fin m → X × X', Φ F) = ∑ f : Fin m → X, ∑ f' : Fin m → X', Φ (zipTraj f f') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (zipEquiv X X' m) (fun p => Φ (zipTraj p.1 p.2)) Φ
    (fun _ => rfl)).symm

/-- **Energy of the normalised flow, pointwise.** -/
theorem flow_energy_le_marked {d : ℕ} {X Γ E : Type*} [Fintype X] [Fintype Γ] [Fintype E]
    (z : Configuration d × Configuration d) (m : ℕ)
    (μ : Γ → ℝ) (hμ : ∀ γ, 0 ≤ μ γ) (wv : Γ → ℝ) (hwv : ∀ γ, 0 ≤ wv γ)
    (k : Γ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ γ t x y z, 0 ≤ k γ t x y z) (x₀ : Γ → X)
    (acond : E → ℝ) (θ : Γ × (Fin m → X) → E → ℝ) (P : Γ × (Fin m → X) → Finset E)
    (hθ : ∀ i e, |θ i e| ≤ if e ∈ P i then (1:ℝ) else 0)
    (hopen : ∀ i e, e ∈ P i → acond e = 1)
    (hW : (1/2:ℝ) ≤ ∑ i : Γ × (Fin m → X),
      μ i.1 * (wv i.1 * trajWeight (k i.1) m 0 (x₀ i.1) i.2 z))
    (e : Γ → Γ → ℕ → X × X → X × X → Configuration d × Configuration d → ℝ)
    {Pb : ℝ}
    (hoverlap : ∀ (γ γ' : Γ) (f f' : Fin m → X),
      0 < μ γ * (wv γ * trajWeight (k γ) m 0 (x₀ γ) f z) →
      0 < μ γ' * (wv γ' * trajWeight (k γ') m 0 (x₀ γ') f' z) →
      (((P (γ, f) ∩ P (γ', f')).card : ℝ)) ≤
        Pb * trajCount (e γ γ') m 0 (x₀ γ, x₀ γ') (zipTraj f f') z) :
    flowEnergy acond (normalizedFlow
        (fun i : Γ × (Fin m → X) => μ i.1 * (wv i.1 * trajWeight (k i.1) m 0 (x₀ i.1) i.2 z)) θ) ≤
      4 * (Pb * ∑ γ, ∑ γ', (μ γ * μ γ') * ((wv γ * wv γ') *
        markedValue (pairKernel (k γ) (k γ'))
          (fun t x y z => pairKernel (k γ) (k γ') t x y z * e γ γ' t x y z) m 0
          (x₀ γ, x₀ γ') z)) := by
  have hwt0 : ∀ i : Γ × (Fin m → X),
      0 ≤ μ i.1 * (wv i.1 * trajWeight (k i.1) m 0 (x₀ i.1) i.2 z) := fun i =>
    mul_nonneg (hμ i.1) (mul_nonneg (hwv i.1) (trajWeight_nonneg (k i.1) (hk i.1) m 0 _ _ z))
  have h1 := normalized_path_flow_energy_le_four_overlaps acond
    (fun i : Γ × (Fin m → X) => μ i.1 * (wv i.1 * trajWeight (k i.1) m 0 (x₀ i.1) i.2 z))
    θ P hwt0 hW hθ hopen
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  -- bound each pair term by the marked count
  have hterm : ∀ (γ γ' : Γ) (f f' : Fin m → X),
      μ γ * (wv γ * trajWeight (k γ) m 0 (x₀ γ) f z) *
        (μ γ' * (wv γ' * trajWeight (k γ') m 0 (x₀ γ') f' z)) *
        ((P (γ, f) ∩ P (γ', f')).card : ℝ) ≤
      μ γ * (wv γ * trajWeight (k γ) m 0 (x₀ γ) f z) *
        (μ γ' * (wv γ' * trajWeight (k γ') m 0 (x₀ γ') f' z)) *
        (Pb * trajCount (e γ γ') m 0 (x₀ γ, x₀ γ') (zipTraj f f') z) := by
    intro γ γ' f f'
    have ha := hwt0 (γ, f)
    have hb := hwt0 (γ', f')
    rcases eq_or_lt_of_le ha with h0 | hpos
    · have h0' : μ γ * (wv γ * trajWeight (k γ) m 0 (x₀ γ) f z) = 0 := h0.symm
      rw [h0']
      simp
    · rcases eq_or_lt_of_le hb with h0 | hpos'
      · have h0' : μ γ' * (wv γ' * trajWeight (k γ') m 0 (x₀ γ') f' z) = 0 := h0.symm
        rw [h0']
        simp
      · exact mul_le_mul_of_nonneg_left (hoverlap γ γ' f f' hpos hpos') (mul_nonneg ha hb)
  have hpairsum : ∀ γ γ' : Γ,
      (∑ f : Fin m → X, ∑ f' : Fin m → X,
        μ γ * (wv γ * trajWeight (k γ) m 0 (x₀ γ) f z) *
          (μ γ' * (wv γ' * trajWeight (k γ') m 0 (x₀ γ') f' z)) *
          (Pb * trajCount (e γ γ') m 0 (x₀ γ, x₀ γ') (zipTraj f f') z)) =
      Pb * ((μ γ * μ γ') * ((wv γ * wv γ') *
        markedValue (pairKernel (k γ) (k γ'))
          (fun t x y z => pairKernel (k γ) (k γ') t x y z * e γ γ' t x y z) m 0
          (x₀ γ, x₀ γ') z)) := by
    intro γ γ'
    rw [markedValue_eq_sum_traj, sum_pair_traj]
    simp only [trajMarked_eq_weight_mul_count, trajWeight_pair]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun f' _ => by ring))
  calc (∑ i : Γ × (Fin m → X), ∑ j : Γ × (Fin m → X),
        μ i.1 * (wv i.1 * trajWeight (k i.1) m 0 (x₀ i.1) i.2 z) *
          (μ j.1 * (wv j.1 * trajWeight (k j.1) m 0 (x₀ j.1) j.2 z)) *
          ((P i ∩ P j).card : ℝ))
      ≤ ∑ i : Γ × (Fin m → X), ∑ j : Γ × (Fin m → X),
        μ i.1 * (wv i.1 * trajWeight (k i.1) m 0 (x₀ i.1) i.2 z) *
          (μ j.1 * (wv j.1 * trajWeight (k j.1) m 0 (x₀ j.1) j.2 z)) *
          (Pb * trajCount (e i.1 j.1) m 0 (x₀ i.1, x₀ j.1) (zipTraj i.2 j.2) z) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i.1 j.1 i.2 j.2))
    _ = ∑ γ, ∑ γ', ∑ f : Fin m → X, ∑ f' : Fin m → X,
        μ γ * (wv γ * trajWeight (k γ) m 0 (x₀ γ) f z) *
          (μ γ' * (wv γ' * trajWeight (k γ') m 0 (x₀ γ') f' z)) *
          (Pb * trajCount (e γ γ') m 0 (x₀ γ, x₀ γ') (zipTraj f f') z) := by
        simp only [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl (fun γ _ => Finset.sum_comm)
    _ = ∑ γ, ∑ γ', Pb * ((μ γ * μ γ') * ((wv γ * wv γ') *
        markedValue (pairKernel (k γ) (k γ'))
          (fun t x y z => pairKernel (k γ) (k γ') t x y z * e γ γ' t x y z) m 0
          (x₀ γ, x₀ γ') z)) :=
        Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun γ' _ => hpairsum γ γ'))
    _ = _ := by
        simp only [Finset.mul_sum]

end NearCritical.Section10
