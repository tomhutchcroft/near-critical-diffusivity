module

public import NearCritical.ChemicalCoarseBox
public import NearCritical.NestCubeWeights
public import NearCritical.BulkDomain

/-! Disjointness of source coarse cubes and their literal internal bonds,
feeding the actual percolation cube-weight factor in lem.nw.mean. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory

lemma internalBondSet_disjoint_of_disjoint {d : ℕ} {U V : Finset (Vertex d)}
    (h : Disjoint U V) : Disjoint (internalBondSet U) (internalBondSet V) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h ((mem_internalBondSet U e).1 he).1
    ((mem_internalBondSet V e).1 hf).1

/-- Distinct mesh-2t cubes of odd side2r+1 are disjoint if r<t. -/
theorem chemicalCoarseCubes_disjoint {d t r : ℕ} (hsmall : r<t)
    {a b : Fin d → ℕ} (hab : a≠b) :
    Disjoint (translateSites (chemicalCoarseCenter t a) (centeredBox d r))
      (translateSites (chemicalCoarseCenter t b) (centeredBox d r)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨u,hu,heua⟩ := Finset.mem_image.mp hxa
  obtain ⟨v,hv,hevb⟩ := Finset.mem_image.mp hxb
  have hcoord : ∃ j, a j≠b j := by
    by_contra h
    apply hab
    funext j
    by_contra hj
    exact h ⟨j,hj⟩
  obtain ⟨j,hj⟩ := hcoord
  have huj := mem_centeredBox.mp hu j
  have hvj := mem_centeredBox.mp hv j
  have he := congrFun (heua.trans hevb.symm) j
  change ((2*t*a j:ℕ):ℤ)+u j = ((2*t*b j:ℕ):ℤ)+v j at he
  have htZ : (r:ℤ)<t := by exact_mod_cast hsmall
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · have hg : 2*t+2*t*a j ≤ 2*t*b j := by
      nlinarith [Nat.mul_le_mul_left (2*t) (show a j+1≤b j by omega)]
    have hgZ : ((2*t+2*t*a j:ℕ):ℤ) ≤ (2*t*b j:ℕ) := by exact_mod_cast hg
    push_cast at he hgZ
    nlinarith
  · have hg : 2*t+2*t*b j ≤ 2*t*a j := by
      nlinarith [Nat.mul_le_mul_left (2*t) (show b j+1≤a j by omega)]
    have hgZ : ((2*t+2*t*b j:ℕ):ℤ) ≤ (2*t*a j:ℕ) := by exact_mod_cast hg
    push_cast at he hgZ
    nlinarith

/-- Source E(Q), not the larger issued bond set E+(Q). -/
def chemicalCoarseInternalBonds (d t r : ℕ) (a : Fin d → ℕ) : Finset (Bond d) :=
  internalBondSet (translateSites (chemicalCoarseCenter t a) (centeredBox d r))

lemma chemicalCoarseInternalBonds_disjoint {d t r : ℕ} (hsmall : r<t)
    {a b : Fin d → ℕ} (hab : a≠b) :
    Disjoint (chemicalCoarseInternalBonds d t r a) (chemicalCoarseInternalBonds d t r b) :=
  internalBondSet_disjoint_of_disjoint (chemicalCoarseCubes_disjoint hsmall hab)

/-- Nearest odd side to t with ties rounded upward: microscopic radius floor(t/2).
It differs from t by at most one and fits strictly inside mesh2t for t>=1. -/
lemma chemicalMicroscopic_rounding {t : ℕ} (ht : 1≤t) :
    t ≤ 2*(t/2)+1 ∧ 2*(t/2)+1 ≤ t+1 ∧ t/2<t := by omega

/-- Actual normalized cube-weight mean for any finite route of distinct source
coarse cubes. Block disjointness and independence are proved, not inputs. -/
theorem percolation_coarseCubeWeight_mean {d t r : ℕ} (p : unitInterval)
    (hsmall : r<t) (route : Finset (Fin d → ℕ))
    (A : ∀ a, Set (chemicalCoarseInternalBonds d t r a → Bool))
    (hq : ∀ a∈route, 0<nestCubeProbability p (chemicalCoarseInternalBonds d t r a) (A a)) :
    (∫ ω : Configuration d, ∏ a∈route,
      nestCubeWeight p (chemicalCoarseInternalBonds d t r a) (A a) ω ∂percolation d p)=1 := by
  apply percolation_nestCubeWeight_product_mean p route _ A _ hq
  intro a ha b hb hab
  exact chemicalCoarseInternalBonds_disjoint hsmall hab

/-- The source nearest-odd microscopic rounding automatically discharges separation. -/
theorem percolation_roundedCoarseCubeWeight_mean {d t : ℕ} (p : unitInterval)
    (ht : 1≤t) (route : Finset (Fin d → ℕ))
    (A : ∀ a, Set (chemicalCoarseInternalBonds d t (t/2) a → Bool))
    (hq : ∀ a∈route, 0<nestCubeProbability p (chemicalCoarseInternalBonds d t (t/2) a) (A a)) :
    (∫ ω : Configuration d, ∏ a∈route,
      nestCubeWeight p (chemicalCoarseInternalBonds d t (t/2) a) (A a) ω ∂percolation d p)=1 :=
  percolation_coarseCubeWeight_mean p (chemicalMicroscopic_rounding ht).2.2 route A hq

end NearCritical
