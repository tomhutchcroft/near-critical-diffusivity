module

public import NearCritical.Section10SiteWeights
public import NearCritical.Section9PivotOpening

/-! Opening one of finitely many fresh bonds, under the coupled law.

For the supercritical configuration `z.1 OR z.2`:
* `or_closed_integral`: a bond is closed with probability `(1 - p)(1 - q)`;
* `all_closed_integral`: all bonds of a finite set are closed with probability
  `((1 - p)(1 - q)) ^ n`;
* `exists_open_integral`: some bond of the set is open with probability
  `1 - ((1 - p)(1 - q)) ^ n`.
This is the computation `s_n = 1 - (1 - p)^{|PTR|}` of the exit step (5487).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- First-layer marginal of the coupled law. -/
lemma integral_fst_layer {d : ℕ} (p q : unitInterval) (g : Configuration d → ℝ)
    (hg : Integrable (fun z : Configuration d × Configuration d => g z.1)
      ((percolation d p).prod (percolation d q))) :
    (∫ z : Configuration d × Configuration d, g z.1
      ∂((percolation d p).prod (percolation d q))) = ∫ ω, g ω ∂(percolation d p) := by
  rw [integral_prod _ hg]
  simp only [integral_const, probReal_univ, one_smul]

/-- Second-layer marginal of the coupled law. -/
lemma integral_snd_layer {d : ℕ} (p q : unitInterval) (g : Configuration d → ℝ)
    (hg : Integrable (fun z : Configuration d × Configuration d => g z.2)
      ((percolation d p).prod (percolation d q))) :
    (∫ z : Configuration d × Configuration d, g z.2
      ∂((percolation d p).prod (percolation d q))) = ∫ ω, g ω ∂(percolation d q) := by
  rw [integral_prod _ hg]
  simp only [integral_const, probReal_univ, one_smul]

/-- A bond is closed with probability `1 - p`. -/
lemma percolation_closed_bond_integral (d : ℕ) (p : unitInterval) (e : Bond d) :
    (∫ ω, (if ω e = false then (1:ℝ) else 0) ∂(percolation d p)) = 1 - (p : ℝ) := by
  have hmeas : MeasurableSet {ω : Configuration d | ω e = true} := by
    have h := (measurable_pi_apply (X := fun _ : Bond d => Bool) e) (measurableSet_singleton true)
    exact h
  have hopen : (percolation d p).real {ω : Configuration d | ω e = true} = (p : ℝ) := by
    unfold Measure.real
    rw [percolation_open_bond, ENNReal.toReal_ofReal p.2.1]
  have hfun : (fun ω : Configuration d => if ω e = false then (1:ℝ) else 0) =
      fun ω => 1 - Set.indicator {ω : Configuration d | ω e = true} (fun _ => (1:ℝ)) ω := by
    funext ω
    by_cases h : ω e = true
    · rw [Set.indicator_of_mem (by exact h), if_neg (by simp [h])]
      ring
    · rw [Set.indicator_of_notMem (by exact h), if_pos (by simpa using h)]
      ring
  rw [hfun, integral_sub (integrable_const _) ((integrable_const _).indicator hmeas),
    integral_indicator_const _ hmeas]
  simp [hopen]

lemma layerClosed_isLocal {d : ℕ} (e : LBond d) :
    IsLocal ({e} : Finset (LBond d)) (fun z => if layerVal z e = false then (1:ℝ) else 0) :=
  ⟨fun b => if b ⟨e, Finset.mem_singleton_self e⟩ = false then (1:ℝ) else 0, fun _ => rfl⟩

/-- A bond is closed in both layers with probability `(1 - p)(1 - q)`. -/
theorem or_closed_integral {d : ℕ} (p q : unitInterval) (b : Bond d) :
    (∫ z : Configuration d × Configuration d,
      (if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))) = (1 - (p:ℝ)) * (1 - (q:ℝ)) := by
  have hfun : (fun z : Configuration d × Configuration d =>
      if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0) =
      fun z => (if layerVal z ((false, b) : LBond d) = false then (1:ℝ) else 0) *
        (if layerVal z ((true, b) : LBond d) = false then (1:ℝ) else 0) := by
    funext z
    show (if (z.1 b || z.2 b) = false then (1:ℝ) else 0) =
      (if z.1 b = false then (1:ℝ) else 0) * (if z.2 b = false then (1:ℝ) else 0)
    cases z.1 b <;> cases z.2 b <;> simp
  have hd : Disjoint ({((false, b) : LBond d)} : Finset (LBond d)) {((true, b) : LBond d)} := by
    simp
  rw [hfun, IsLocal.integral_mul p q hd (layerClosed_isLocal _) (layerClosed_isLocal _)]
  have h1 := integral_fst_layer p q (fun ω => if ω b = false then (1:ℝ) else 0)
    ((layerClosed_isLocal ((false, b) : LBond d)).integrable p q)
  have h2 := integral_snd_layer p q (fun ω => if ω b = false then (1:ℝ) else 0)
    ((layerClosed_isLocal ((true, b) : LBond d)).integrable p q)
  rw [percolation_closed_bond_integral] at h1 h2
  show (∫ z : Configuration d × Configuration d, (if z.1 b = false then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))) *
    (∫ z : Configuration d × Configuration d, (if z.2 b = false then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))) = _
  rw [h1, h2]

lemma orClosed_isLocal {d : ℕ} (b : Bond d) :
    IsLocal ({((false, b) : LBond d), ((true, b) : LBond d)} : Finset (LBond d))
      (fun z => if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0) :=
  ⟨fun v => if (v ⟨(false, b), by simp⟩ || v ⟨(true, b), by simp⟩) = false then (1:ℝ) else 0,
    fun _ => rfl⟩

/-- All bonds of a finite set are closed in both layers. -/
theorem all_closed_integral {d : ℕ} (p q : unitInterval) (Y : Finset (Bond d)) :
    (∫ z : Configuration d × Configuration d,
      ∏ b ∈ Y, (if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ((1 - (p:ℝ)) * (1 - (q:ℝ))) ^ Y.card := by
  rw [integral_finset_prod p q
    (fun b : Bond d => ({((false, b) : LBond d), ((true, b) : LBond d)} : Finset (LBond d)))
    (fun a b hab => by
      rw [Finset.disjoint_left]
      intro e he he'
      simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
      rcases he with rfl | rfl <;> rcases he' with h | h <;>
        exact hab (Prod.mk.inj h).2)
    (fun b z => if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0)
    orClosed_isLocal Y]
  rw [Finset.prod_congr rfl (fun b _ => or_closed_integral p q b), Finset.prod_const]

/-- Some bond of a finite set is open in the supercritical configuration. -/
theorem exists_open_integral {d : ℕ} (p q : unitInterval) (Y : Finset (Bond d)) :
    (∫ z : Configuration d × Configuration d,
      (if ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))) =
      1 - ((1 - (p:ℝ)) * (1 - (q:ℝ))) ^ Y.card := by
  have hfun : (fun z : Configuration d × Configuration d =>
      if ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true then (1:ℝ) else 0) =
      fun z => 1 - ∏ b ∈ Y, (if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0) := by
    funext z
    by_cases h : ∃ b ∈ Y, sprinkleOrConfiguration z.1 z.2 b = true
    · rw [if_pos h]
      obtain ⟨b, hb, hopen⟩ := h
      rw [Finset.prod_eq_zero hb (by simp [hopen])]
      ring
    · rw [if_neg h]
      have hall : ∀ b ∈ Y, (if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0) = 1 := by
        intro b hb
        have : sprinkleOrConfiguration z.1 z.2 b = false := by
          by_contra hne
          exact h ⟨b, hb, by simpa using hne⟩
        rw [if_pos this]
      rw [Finset.prod_congr rfl hall, Finset.prod_const_one]
      ring
  have hloc : IsLocal (Y.biUnion fun b : Bond d =>
      ({((false, b) : LBond d), ((true, b) : LBond d)} : Finset (LBond d)))
      (fun z => ∏ b ∈ Y, (if sprinkleOrConfiguration z.1 z.2 b = false then (1:ℝ) else 0)) :=
    isLocal_finset_prod _ _ orClosed_isLocal Y
  rw [hfun, integral_sub (integrable_const _) (hloc.integrable p q), all_closed_integral]
  simp

end NearCritical.Section10
