module
public import NearCritical.ProfileDomainLocalization
public import NearCritical.ProfileSlabPioneer

/-! Literal source eq.def.A.inhomo. q is used ONLY when both bond endpoints
lie in S_(m+1,n); interface-crossing bonds retain p. Exact homogeneous law
identifications below are proved under the actual infinite product measure. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

def twoPhaseSlabProfile {d : ℕ} (i : Fin d) (m n : ℤ) (p q : unitInterval) :
    Bond d → unitInterval := fun e =>
  if e.1 ∈ finiteHeightSlab i (m+1) n ∧ bondTip e ∈ finiteHeightSlab i (m+1) n then q else p

def twoPhaseSlabPioneerMass {d : ℕ} (i : Fin d) (p q : unitInterval)
    (m n k j : ℤ) : ℝ≥0∞ :=
  profileSlabPioneerMass (twoPhaseSlabProfile i m n p q) i 0 n k j

lemma twoPhaseSlabProfile_self {d : ℕ} (i : Fin d) (m n : ℤ) (p : unitInterval) :
    twoPhaseSlabProfile i m n p p = fun _ => p := by
  funext e
  simp [twoPhaseSlabProfile]

lemma twoPhaseSlabProfile_of_upper_le_interface {d : ℕ} (i : Fin d) {m n : ℤ}
    (hnm : n ≤ m) (p q : unitInterval) :
    twoPhaseSlabProfile i m n p q = fun _ => p := by
  funext e
  have hnot : ¬(e.1 ∈ finiteHeightSlab i (m+1) n ∧ bondTip e ∈ finiteHeightSlab i (m+1) n) := by
    rintro ⟨he,_⟩
    change m+1 ≤ e.1 i ∧ e.1 i ≤ n at he
    omega
  simp only [twoPhaseSlabProfile,hnot,ite_false]

/-- This includes L_m horizontal bonds and the L_m-to-L_(m+1) crossing bond. -/
lemma twoPhaseSlabProfile_at_interface {d : ℕ} (i : Fin d) (m n : ℤ)
    (p q : unitInterval) (e : Bond d) (he : e.1 i = m) :
    twoPhaseSlabProfile i m n p q e = p := by
  have hnot : ¬(e.1 ∈ finiteHeightSlab i (m+1) n ∧ bondTip e ∈ finiteHeightSlab i (m+1) n) := by
    rintro ⟨h,_⟩
    change m+1 ≤ e.1 i ∧ e.1 i ≤ n at h
    omega
  simp only [twoPhaseSlabProfile,hnot,ite_false]

lemma twoPhaseSlabPioneerMass_self {d : ℕ} (i : Fin d) (p : unitInterval)
    (m n k j : ℤ) :
    twoPhaseSlabPioneerMass i p p m n k j = slabPioneerMass p i 0 n k j := by
  rw [twoPhaseSlabPioneerMass,twoPhaseSlabProfile_self,profileSlabPioneerMass_const]

lemma twoPhaseSlabPioneerMass_of_upper_le_interface {d : ℕ} (i : Fin d)
    (p q : unitInterval) {m n : ℤ} (hnm : n ≤ m) (k j : ℤ) :
    twoPhaseSlabPioneerMass i p q m n k j = slabPioneerMass p i 0 n k j := by
  rw [twoPhaseSlabPioneerMass,twoPhaseSlabProfile_of_upper_le_interface i hnm,
    profileSlabPioneerMass_const]

/-- Actual q-law for paths entirely inside the strict upper phase, including
zero-length connections and arbitrary target sets. -/
theorem twoPhaseSlab_connection_upper_law {d : ℕ} (i : Fin d) (m n : ℤ)
    (p q : unitInterval) (S : Set (Vertex d)) (hS : S ⊆ finiteHeightSlab i (m+1) n)
    (x : Vertex d) (A : Set (Vertex d)) :
    percolationProfile d (twoPhaseSlabProfile i m n p q) (connectionToSetEvent S x A) =
      percolation d q (connectionToSetEvent S x A) := by
  exact connectionToSet_profile_eq_of_internal_rates S _ (fun _ => q)
    (fun e he => by simp only [twoPhaseSlabProfile,hS he.1,hS he.2,and_self,ite_true]) x A

/-- Actual p-law for paths confined at or below the interface. -/
theorem twoPhaseSlab_connection_lower_law {d : ℕ} (i : Fin d) (m n : ℤ)
    (p q : unitInterval) (S : Set (Vertex d)) (hS : S ⊆ {x | x i ≤ m})
    (x : Vertex d) (A : Set (Vertex d)) :
    percolationProfile d (twoPhaseSlabProfile i m n p q) (connectionToSetEvent S x A) =
      percolation d p (connectionToSetEvent S x A) := by
  apply connectionToSet_profile_eq_of_internal_rates S _ (fun _ => p)
  intro e he
  have htail : e.1 i ≤ m := hS he.1
  have hnot : ¬(e.1 ∈ finiteHeightSlab i (m+1) n ∧ bondTip e ∈ finiteHeightSlab i (m+1) n) := by
    rintro ⟨h,_⟩
    change m+1 ≤ e.1 i ∧ e.1 i ≤ n at h
    omega
  simp only [twoPhaseSlabProfile,hnot,ite_false]

/-- Exact source suffix-law identification in critical Case(b). -/
theorem twoPhaseSlab_suffix_law {d : ℕ} (i : Fin d) (m j n : ℤ) (hjn : j ≤ n)
    (p q : unitInterval) (x : Vertex d) (A : Set (Vertex d)) :
    percolationProfile d (twoPhaseSlabProfile i m n p q)
      (connectionToSetEvent (finiteHeightSlab i (m+1) j) x A) =
    percolation d q (connectionToSetEvent (finiteHeightSlab i (m+1) j) x A) := by
  apply twoPhaseSlab_connection_upper_law
  intro z hz
  change m+1 ≤ z i ∧ z i ≤ n
  exact ⟨hz.1,hz.2.trans hjn⟩

/-- Changing the unused upper cap does not change the law of a restricted
path below an intermediate level. This makes source prefix A notation exact. -/
theorem twoPhaseSlab_connection_cutoff_law {d : ℕ} (i : Fin d) (m j n : ℤ)
    (hjn : j ≤ n) (p q : unitInterval) (S : Set (Vertex d))
    (hS : S ⊆ {z | z i ≤ j}) (x : Vertex d) (A : Set (Vertex d)) :
    percolationProfile d (twoPhaseSlabProfile i m n p q) (connectionToSetEvent S x A) =
      percolationProfile d (twoPhaseSlabProfile i m j p q) (connectionToSetEvent S x A) := by
  apply connectionToSet_profile_eq_of_internal_rates
  intro e he
  have hx : e.1 i ≤ j := hS he.1
  have hy : bondTip e i ≤ j := hS he.2
  simp [twoPhaseSlabProfile,finiteHeightSlab,hx,hy,hx.trans hjn,hy.trans hjn]

theorem twoPhaseSlabPioneerMass_prefix_law {d : ℕ} (i : Fin d) (m j n : ℤ)
    (hjn : j ≤ n) (p q : unitInterval) (k t : ℤ) :
    profileSlabPioneerMass (twoPhaseSlabProfile i m n p q) i 0 j k t =
      twoPhaseSlabPioneerMass i p q m j k t := by
  unfold profileSlabPioneerMass twoPhaseSlabPioneerMass
  apply tsum_congr
  intro u
  split_ifs
  · exact twoPhaseSlab_connection_cutoff_law i m j n hjn p q _
      (fun z hz => hz.2) _ _
  · rfl

/-- Literal source d_m(k,j): distance after truncating heights below m. -/
def twoPhaseSlabDistance (m k j : ℤ) : ℝ :=
  |((j-m).toNat:ℝ)-((k-m).toNat:ℝ)|

lemma twoPhaseSlabDistance_symm (m k j : ℤ) :
    twoPhaseSlabDistance m k j = twoPhaseSlabDistance m j k := abs_sub_comm _ _

lemma twoPhaseSlabDistance_triangle (m k j t : ℤ) :
    twoPhaseSlabDistance m k j ≤ twoPhaseSlabDistance m k t+twoPhaseSlabDistance m t j := by
  simpa only [twoPhaseSlabDistance,add_comm] using
    abs_sub_le ((j-m).toNat:ℝ) ((t-m).toNat:ℝ) ((k-m).toNat:ℝ)

lemma twoPhaseSlabDistance_below {m k j : ℤ} (hk : k ≤ m) (hj : j ≤ m) :
    twoPhaseSlabDistance m k j = 0 := by
  have hk0 : (k-m).toNat = 0 := by omega
  have hj0 : (j-m).toNat = 0 := by omega
  simp [twoPhaseSlabDistance,hk0,hj0]

lemma twoPhaseSlabDistance_crossing {m k j : ℤ} (hk : k ≤ m) (hj : m ≤ j) :
    twoPhaseSlabDistance m k j = (j:ℝ)-(m:ℝ) := by
  have hk0 : (k-m).toNat = 0 := by omega
  have hjr : ((j-m).toNat:ℝ) = (j:ℝ)-(m:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ j-m by omega)
  rw [twoPhaseSlabDistance,hk0,Nat.cast_zero,sub_zero,hjr,abs_of_nonneg]
  exact_mod_cast (show 0 ≤ j-m by omega)

/-- Polynomial domination only; no exponential inhomogeneous gain is asserted. -/
theorem twoPhaseSlabPioneerMass_le_homogeneous {d : ℕ} (i : Fin d)
    (p q : unitInterval) (hqp : q ≤ p) (m n k j : ℤ) :
    twoPhaseSlabPioneerMass i p q m n k j ≤ slabPioneerMass p i 0 n k j := by
  apply profileSlabPioneerMass_le_homogeneous _ p _ i 0 n k j
  intro e
  unfold twoPhaseSlabProfile
  split
  · exact hqp
  · exact le_rfl

end NearCritical
