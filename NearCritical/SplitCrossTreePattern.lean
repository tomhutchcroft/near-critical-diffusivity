module

public import NearCritical.SplitCrossBranchPattern

/-! A family of local branch patterns can be prescribed at once. The union
of their incident bond masks is disjoint from the bonds of the outside graph. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical

variable {d : ℕ} {ι : Type*}

def treeMoatVertices (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) : Finset (Vertex d) :=
  I.biUnion (fun i => branchMoatVertices (b i) axes R r)

def treeGuardBonds (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) : Finset (Bond d) :=
  I.biUnion (fun i => branchGuardBonds (b i) axes R r)

def treeOpenBonds (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) : Finset (Bond d) :=
  I.biUnion (fun i => starBonds (b i) axes (R + r))

def treeBranchPattern (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) : Set (Configuration d) :=
  (treeGuardBonds I b axes R r).restrict ⁻¹'
    ({(fun e : ↥(treeGuardBonds I b axes R r) => decide (e.val ∈ treeOpenBonds I b axes R r))} :
      Set (↥(treeGuardBonds I b axes R r) → Bool))

theorem treeGuard_disjoint_outside (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) (U : Finset (Vertex d)) :
    Disjoint (treeGuardBonds I b axes R r)
      (internalBondSet (U \ treeMoatVertices I b axes R r)) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  have hs : U \ treeMoatVertices I b axes R r ⊆ U \ branchMoatVertices (b i) axes R r := by
    intro x hx
    have ⟨hxU, hxF⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxU, fun h => hxF (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)⟩
  obtain ⟨hb, ht⟩ := (mem_internalBondSet _ _).mp he'
  exact Finset.disjoint_left.mp (branchGuard_disjoint_outside (b i) axes R r U) hei
    ((mem_internalBondSet _ _).mpr ⟨hs hb, hs ht⟩)

theorem treeGuardBonds_card_le (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) :
    (treeGuardBonds I b axes R r).card ≤
      I.card * ((axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d)) := by
  unfold treeGuardBonds
  refine Finset.card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _i ∈ I, (axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d) :=
      Finset.sum_le_sum (fun i _ => branchGuardBonds_card_le (b i) axes R r)
    _ = _ := by simp

/-- Separated branch positions allow the combined assignment to realize
every local pattern simultaneously. -/
theorem treeBranchPattern_local (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → 2 * ((R + r + 1 : ℕ) : ℝ) < dist (b i) (b j))
    {ω : Configuration d} (hω : ω ∈ treeBranchPattern I b axes R r) {i : ι} (hi : i ∈ I) :
    ω ∈ branchPattern (b i) axes R r := by
  have hη : (treeGuardBonds I b axes R r).restrict ω =
      (fun f : ↥(treeGuardBonds I b axes R r) => decide (f.val ∈ treeOpenBonds I b axes R r)) :=
    Set.mem_singleton_iff.mp hω
  apply Set.mem_singleton_iff.mpr
  funext e
  have hstate := congrFun hη ⟨e.val, Finset.mem_biUnion.mpr ⟨i, hi, e.property⟩⟩
  have hEq : e.val ∈ treeOpenBonds I b axes R r ↔ e.val ∈ starBonds (b i) axes (R + r) := by
    constructor
    · intro he
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
      by_cases hij : i = j
      · simpa [hij] using hej
      · exact (Finset.disjoint_left.mp (branchGuards_disjoint axes R r (hsep i hi j hj hij))
          e.property (extendedStarBonds_subset_branchGuard (b j) axes R r hej)).elim
    · intro he
      exact Finset.mem_biUnion.mpr ⟨i, hi, he⟩
  simpa [Finset.restrict, hEq] using hstate

theorem treeExitTip_mem_outside (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R : ℕ) {r : ℕ} (hr : 0 < r)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → 2 * ((R + r + 1 : ℕ) : ℝ) < dist (b i) (b j))
    {i : ι} (hi : i ∈ I) {a : Fin d} (ha : a ∈ axes) (U : Finset (Vertex d))
    (hU : starTip (b i) a (R + r) ∈ U) :
    starTip (b i) a (R + r) ∈ U \ treeMoatVertices I b axes R r := by
  refine Finset.mem_sdiff.mpr ⟨hU, ?_⟩
  intro hm
  obtain ⟨j, hj, hv⟩ := Finset.mem_biUnion.mp hm
  by_cases hij : i = j
  · subst j
    exact branchExitTip_not_mem_moat (b i) axes a R hr hv
  · let k := R + r - 1
    let e : Bond d := (starTip (b i) a k, a)
    have hk : k < R + r := by dsimp [k]; omega
    have he : e ∈ starBonds (b i) axes (R + r) := Finset.mem_biUnion.mpr
      ⟨a, ha, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩
    have htip : bondTip e = starTip (b i) a (R + r) := by
      change bondTip (starTip (b i) a k, a) = _
      rw [rayBond_tip, show k + 1 = R + r by omega]
    have he' : e ∈ branchGuardBonds (b j) axes R r :=
      Finset.mem_biUnion.mpr ⟨starTip (b i) a (R + r), hv,
        (External.mem_vertexIncidentBonds _ _).mpr (Or.inr htip)⟩
    exact Finset.disjoint_left.mp (branchGuards_disjoint axes R r (hsep i hi j hj hij))
      (extendedStarBonds_subset_branchGuard (b i) axes R r he) he'

/-- Prescribing every branch costs a single positive finite-energy constant,
uniform in the positions, on the disjoint outside event. -/
theorem treeBranchPattern_with_outside_lower (p : unitInterval) (I : Finset ι) (b : ι → Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) (U : Finset (Vertex d))
    (A : Set (↥(internalBondSet (U \ treeMoatVertices I b axes R r)) → Bool)) :
    let T := internalBondSet (U \ treeMoatVertices I b axes R r)
    (min (p : ℝ) (1 - (p : ℝ))) ^
        (I.card * ((axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d))) *
        (percolation d p).real (T.restrict ⁻¹' A) ≤
      (percolation d p).real (treeBranchPattern I b axes R r ∩ T.restrict ⁻¹' A) := by
  intro T
  unfold treeBranchPattern
  rw [prescribed_bonds_factor p _ T (treeGuard_disjoint_outside I b axes R r U)]
  exact mul_le_mul_of_nonneg_right
    (prescribed_bonds_probability_lower p _ _ (treeGuardBonds_card_le I b axes R r))
    measureReal_nonneg

end NearCritical.SplitCrossDirect
