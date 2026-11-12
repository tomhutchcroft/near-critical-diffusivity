module

public import NearCritical.AppendixShellCount

/-! Concrete Appendix-B remote-distance (`RD`) geometry: the second-largest absolute
coordinate `a₍₂₎(w)` and `s_w := c₁n - a₍₂₎(w)`, the first ingredients of `eq.RD_count`.

`a₍₂₎(w)` is formalized as `secondMax w`, the max over ordered pairs of distinct coordinates
of the min of their absolute values — the standard "second largest = max of pairwise mins"
characterization. This is the non-probabilistic geometric scaffolding of `eq.RD_count`; the
probabilistic two-point/arm bounds of Appendix B remain Appendix-A territory. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `linfDist 0 w` is the max absolute coordinate `a₍₁₎(w) = max_i |w i|`. -/
theorem linfDist_zero (d : ℕ) (w : Fin d → ℤ) :
    linfDist (0 : Fin d → ℤ) w = Finset.univ.sup (fun i => (w i).natAbs) := by
  rw [linfDist]
  refine Finset.sup_congr rfl (fun i _ => ?_)
  simp

/-- The second-largest absolute coordinate `a₍₂₎(w)`, as the max over distinct coordinate
pairs of the min of their absolute values. -/
def secondMax {d : ℕ} (w : Fin d → ℤ) : ℕ :=
  Finset.univ.sup (fun p : Fin d × Fin d => if p.1 = p.2 then 0 else min (w p.1).natAbs (w p.2).natAbs)

/-- `a₍₂₎(w) ≤ a₍₁₎(w)`: the second-largest absolute coordinate is at most the largest. -/
theorem secondMax_le_linfDist {d : ℕ} (w : Fin d → ℤ) :
    secondMax w ≤ linfDist (0 : Fin d → ℤ) w := by
  rw [secondMax, linfDist_zero, Finset.sup_le_iff]
  intro p _
  by_cases hp : p.1 = p.2
  · simp [hp]
  · rw [if_neg hp]
    exact le_trans (min_le_left _ _) (Finset.le_sup (f := fun i => (w i).natAbs) (Finset.mem_univ p.1))

/-- The remote shortfall `s_w := c₁n - a₍₂₎(w)` (ℕ truncated subtraction), and the
remote-distance predicate `w ∈ RD ↔ r_w < s_w`. Here `rdist` is the given distance `r_w`. -/
def sParam {d : ℕ} (c : ℕ) (w : Fin d → ℤ) : ℕ := c - secondMax w

/-- `s_w ≤ c₁n`, with equality iff `a₍₂₎(w) = 0`. -/
theorem sParam_le {d : ℕ} (c : ℕ) (w : Fin d → ℤ) : sParam c w ≤ c := by
  rw [sParam]; exact Nat.sub_le c (secondMax w)

/-- `a₍₂₎(w)` is realized by some coordinate pair (the sup over a nonempty finite index set). -/
theorem secondMax_eq_sup {d : ℕ} (hd : 0 < d) (w : Fin d → ℤ) :
    ∃ p : Fin d × Fin d,
      secondMax w = (if p.1 = p.2 then 0 else min (w p.1).natAbs (w p.2).natAbs) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d × Fin d))
    Finset.univ_nonempty
    (fun p : Fin d × Fin d => if p.1 = p.2 then 0 else min (w p.1).natAbs (w p.2).natAbs)
  exact ⟨p, by rw [secondMax]; exact hp⟩

/-- The structural meaning of `a₍₂₎(w) ≥ v` (for `v ≥ 1`): at least two distinct coordinates of
`w` have absolute value `≥ v`. This is the combinatorial content behind the `eq.RD_count`
per-shortfall count (`#{w : s_w = s}`): `s_w = s` forces `a₍₂₎(w) = c - s`, i.e. two large
coordinates. -/
theorem exists_pair_ge_of_le_secondMax {d : ℕ} (hd : 0 < d) {w : Fin d → ℤ} {v : ℕ}
    (hv : 1 ≤ v) (hle : v ≤ secondMax w) :
    ∃ i j : Fin d, i ≠ j ∧ v ≤ (w i).natAbs ∧ v ≤ (w j).natAbs := by
  obtain ⟨p, hp⟩ := secondMax_eq_sup hd w
  rw [hp] at hle
  by_cases h : p.1 = p.2
  · rw [if_pos h] at hle; omega
  · rw [if_neg h] at hle
    exact ⟨p.1, p.2, h, le_trans hle (min_le_left _ _), le_trans hle (min_le_right _ _)⟩

/-! ### Concrete cube / half-space / annulus / remote-distance geometry

Faithful to source §"Upper bound for the 2-point function in cubes and annulus": `Q = Λ_m`
is the ℓ∞ cube, `H` a half-space, `int H` its interior, `Ann_{c₁n} = Q \ int H`, `r_w` the
ℓ∞ distance from `w` to `∂H`, `s_w = c₁n - a₍₂₎(w)`, and `RD_{c₁n} = {w ∈ Ann : r_w < s_w}`.
We take the half-space along coordinate `0`: `int H = {w : a < w 0}`, so `∂H = {w : w 0 = a}`
and `r_w = |w 0 - a|`. These concrete definitions discharge the structural region hypotheses
(the `⊆` facts); the sharp `eq.RD_count` cardinality bound (needing the pinned coordinate) and
the probabilistic bounds remain.

CONVENTION / SCOPE WARNING: with the coord-`0` half-space (and `c = a`) this `RD` is a single
INNER pyramid — the mirror of one cube face — NOT the source's `Ann = Λ_n ∖ int Λ_{c₁n}` with its
`2d` OUTER pyramids. So `RD` here, and any count proved over it, is TRUE of this inner-pyramid set
but is NOT literally `eq.RD_count`'s geometry. The LITERAL source geometry (`sourceAnnulus` /
`sourceR` / `sourceRD`) and both halves of `eq.RD_count` proved on it live in `AppendixSourceRD` /
`AppendixSourceRDComplement`; see those for the source statement. -/

/-- The cube `Q = Λ_m`, the ℓ∞ ball of radius `m` about the origin. -/
def cube {d : ℕ} (m : ℕ) : Finset (Fin d → ℤ) := linfBall (0 : Fin d → ℤ) (m : ℤ)

/-- `Q = Λ_m` is literally the ℓ∞ ball, so all ball lemmas apply. -/
theorem cube_eq_linfBall {d : ℕ} (m : ℕ) :
    (cube m : Finset (Fin d → ℤ)) = linfBall (0 : Fin d → ℤ) (m : ℤ) := rfl

/-- The annulus `Ann = Q \ int H = {w ∈ Q : w 0 ≤ a}` (complement of the open half-space
`int H = {w : a < w 0}`). -/
def annulus {d : ℕ} [NeZero d] (m : ℕ) (a : ℤ) : Finset (Fin d → ℤ) :=
  (cube m).filter (fun w => w 0 ≤ a)

/-- `Ann ⊆ Q`: the annulus sits inside the cube (hence inside the ℓ∞ ball). -/
theorem annulus_subset_cube {d : ℕ} [NeZero d] (m : ℕ) (a : ℤ) :
    (annulus m a : Finset (Fin d → ℤ)) ⊆ cube m := by
  unfold annulus; exact Finset.filter_subset _ _

theorem annulus_subset_linfBall {d : ℕ} [NeZero d] (m : ℕ) (a : ℤ) :
    (annulus m a : Finset (Fin d → ℤ)) ⊆ linfBall (0 : Fin d → ℤ) (m : ℤ) := by
  unfold annulus cube; exact Finset.filter_subset _ _

/-- `r_w`: the ℓ∞ distance from `w` to the boundary hyperplane `∂H = {w : w 0 = a}`, which equals
`|w 0 - a|` (the nearest boundary point differs from `w` only in coordinate `0`). -/
def rParam {d : ℕ} [NeZero d] (a : ℤ) (w : Fin d → ℤ) : ℕ := (w 0 - a).natAbs

/-- The remote-distance set `RD_{c₁n} = {w ∈ Ann : r_w < s_w}`. -/
def RD {d : ℕ} [NeZero d] (m : ℕ) (c : ℕ) (a : ℤ) : Finset (Fin d → ℤ) :=
  (annulus m a).filter (fun w => rParam a w < sParam c w)

/-- `RD ⊆ Ann ⊆ Q`. -/
theorem RD_subset_annulus {d : ℕ} [NeZero d] (m c : ℕ) (a : ℤ) :
    (RD m c a : Finset (Fin d → ℤ)) ⊆ annulus m a := by
  unfold RD; exact Finset.filter_subset _ _

theorem RD_subset_cube {d : ℕ} [NeZero d] (m c : ℕ) (a : ℤ) :
    (RD m c a : Finset (Fin d → ℤ)) ⊆ cube m :=
  (RD_subset_annulus m c a).trans (annulus_subset_cube m a)

/-- Membership in the cube `Q = Λ_m`: coordinatewise `|w i| ≤ m`. -/
theorem mem_cube {d : ℕ} {m : ℕ} {w : Fin d → ℤ} :
    w ∈ cube m ↔ ∀ i, |w i| ≤ (m : ℤ) := by
  unfold cube; rw [mem_linfBall]; simp

/-- Membership in the annulus `Ann = Q \ int H`: in the cube and `w 0 ≤ a`. -/
theorem mem_annulus {d : ℕ} [NeZero d] {m : ℕ} {a : ℤ} {w : Fin d → ℤ} :
    w ∈ annulus m a ↔ w ∈ cube m ∧ w 0 ≤ a := by
  unfold annulus; rw [Finset.mem_filter]

/-- Membership in `RD = {w ∈ Ann : r_w < s_w}`. -/
theorem mem_RD {d : ℕ} [NeZero d] {m c : ℕ} {a : ℤ} {w : Fin d → ℤ} :
    w ∈ RD m c a ↔ w ∈ annulus m a ∧ rParam a w < sParam c w := by
  unfold RD; rw [Finset.mem_filter]

/-- Cardinality of the cube `Q = Λ_m`: `(2m+1)^d`. -/
theorem cube_card {d : ℕ} (m : ℕ) : (cube m : Finset (Fin d → ℤ)).card = (2 * m + 1) ^ d := by
  have h : (2 * (m : ℤ) + 1).toNat = 2 * m + 1 := by omega
  rw [cube, linfBall_card, h]

/-- `|Ann| ≤ |Q| = (2m+1)^d`: the annulus is no larger than the cube. -/
theorem annulus_card_le {d : ℕ} [NeZero d] (m : ℕ) (a : ℤ) :
    (annulus m a : Finset (Fin d → ℤ)).card ≤ (2 * m + 1) ^ d := by
  rw [← cube_card m]
  exact Finset.card_le_card (annulus_subset_cube m a)

/-- `|RD| ≤ (2m+1)^d`. -/
theorem RD_card_le {d : ℕ} [NeZero d] (m c : ℕ) (a : ℤ) :
    (RD m c a : Finset (Fin d → ℤ)).card ≤ (2 * m + 1) ^ d := by
  rw [← cube_card m]
  exact Finset.card_le_card (RD_subset_cube m c a)

end NearCritical.AppendixVariance
