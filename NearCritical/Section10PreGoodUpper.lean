module

public import NearCritical.Section10ClusterTranslation
public import NearCritical.PreGoodUpperCount
public import NearCritical.SpanningBoundaryDiameter

/-! Step 3 of `prop.proba.pregood` for the ACTUAL typical family.

* `typicalCube_zero`, `typicalFace_zero`: the origin typical cube is
  `centeredBox d ((t-1)/2)` with its signed faces.
* `typical_count_upper_failure`: at `p_c`, the number of typical clusters of the
  origin cube exceeds `countUpper (2t)^(d-6)` with probability at most `eps/3`,
  provided `27 C / (volumeLower eps) <= countUpper`; input: the cited ordinary
  one-arm window bound.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

lemma translateSites_zero {d : ℕ} (U : Finset (Vertex d)) : translateSites 0 U = U := by
  ext x
  rw [mem_translateSites_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [zero_add]
  · intro hx
    exact ⟨x, hx, zero_add x⟩

theorem typicalCube_zero {d : ℕ} (t : ℕ) (ht : 1 ≤ t) :
    typicalCube t (0 : Vertex d) = centeredBox d ((t - 1) / 2) := by
  ext x
  unfold typicalCube
  rw [Finset.mem_filter, translateSites_zero, mem_centeredBox, mem_centeredBox]
  have key : ∀ j, (2 * |((x j - (0 : Vertex d) j : ℤ) : ℝ)| < (t : ℝ)) ↔
      (-(((t - 1) / 2 : ℕ) : ℤ) ≤ x j ∧ x j ≤ (((t - 1) / 2 : ℕ) : ℤ)) := by
    intro j
    have h1 : (2 * |((x j - (0 : Vertex d) j : ℤ) : ℝ)| < (t : ℝ)) ↔ 2 * |x j| < (t : ℤ) := by
      rw [Pi.zero_apply, sub_zero]
      constructor
      · intro h
        have h' : ((2 * |x j| : ℤ) : ℝ) < ((t : ℤ) : ℝ) := by
          push_cast
          exact h
        exact_mod_cast h'
      · intro h
        have h' : ((2 * |x j| : ℤ) : ℝ) < ((t : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at h'
        exact h'
    rw [h1]
    generalize hr : (t - 1) / 2 = r
    have hr1 : 2 * r + 1 ≤ t := by omega
    have hr2 : t ≤ 2 * r + 2 := by omega
    constructor
    · intro h
      have := abs_lt.mp (by linarith : |x j| < ((r : ℤ) + 1))
      constructor <;> omega
    · rintro ⟨h3, h4⟩
      have : |x j| ≤ (r : ℤ) := abs_le.mpr ⟨h3, h4⟩
      omega
  constructor
  · rintro ⟨_, h⟩ j
    exact (key j).mp (h j)
  · intro h
    refine ⟨fun j => ?_, fun j => (key j).mpr (h j)⟩
    obtain ⟨h3, h4⟩ := h j
    constructor <;> omega

theorem typicalFace_zero {d : ℕ} (t : ℕ) (ht : 1 ≤ t) (face : Fin d × Bool) :
    typicalFace t (0 : Vertex d) face = signedCubeFace d ((t - 1) / 2) face := by
  ext x
  unfold typicalFace signedCubeFace
  rw [Finset.mem_filter, Finset.mem_filter, typicalCube_zero t ht, Pi.zero_apply, sub_zero]

theorem typicalClusterFamily_zero {d : ℕ} (typ : TypicalParameters) (t : ℕ) (ht : 1 ≤ t)
    (ω : Configuration d) :
    typicalClusterFamily typ t (0 : Vertex d) ω =
      filteredClusterFamily ω (centeredBox d ((t - 1) / 2)) (IsTypicalCluster typ t 0 ω) := by
  ext C
  unfold typicalClusterFamily filteredClusterFamily
  rw [Finset.mem_filter, Finset.mem_filter, typicalCube_zero t ht]

/-- **Upper count of `prop.proba.pregood` (Step 3), origin cube.** -/
theorem typical_count_upper_failure {d : ℕ} (i : Fin d) (hd : 6 ≤ d) (typ : TypicalParameters)
    (t : ℕ) (ht : 3 ≤ t) {C ε : ℝ} (hC : 0 < C) (ordinary : OrdinaryArmWindowInput d C)
    (hv : 0 < typ.volumeLower) (hε : 0 < ε)
    (hup : 27 * C / (typ.volumeLower * ε) ≤ typ.countUpper) :
    (percolation d (criticalPoint d)).real
      {ω | ¬ ((typicalClusterFamily typ t (0 : Vertex d) ω).card : ℝ) ≤
        typ.countUpper * (2 * (t : ℝ)) ^ (d - 6)} ≤ ε / 3 := by
  obtain ⟨r, hr⟩ : ∃ r, (t - 1) / 2 = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega
  have hrt : 2 * r + 1 ≤ t := by omega
  have ht1 : 1 ≤ t := by omega
  have hLt : (((2 * r + 1 : ℕ) : ℝ)) ≤ 2 * (t : ℝ) := by
    have h : ((2 * r + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
    have h0 : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hL0 : (0:ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmain := preGood_cluster_count_upper_failure (r := r) i hr1 hd hC ordinary hv hε
    (fun ω => IsTypicalCluster typ t (0 : Vertex d) ω)
    (by
      intro ω E hE
      have hE' : E ∈ typicalClusterFamily typ t (0 : Vertex d) ω := by
        rw [typicalClusterFamily_zero typ t ht1, hr]
        exact hE
      have htyp := ((mem_typicalClusterFamily typ t 0 ω E).mp hE').2
      have h4 : typ.volumeLower * ((2 * r + 1 : ℕ) : ℝ) ^ 4 ≤
          typ.volumeLower * (2 * (t : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLt 4) hv.le
      exact h4.trans htyp.2.2.1.le)
    (by
      intro ω E hE j
      have h := hE.2.1 j
      rwa [typicalFace_zero t ht1, hr] at h)
  refine (measureReal_mono ?_).trans hmain
  intro ω hω
  have hω' : typ.countUpper * (2 * (t : ℝ)) ^ (d - 6) <
      ((typicalClusterFamily typ t (0 : Vertex d) ω).card : ℝ) := not_le.mp hω
  rw [typicalClusterFamily_zero typ t ht1, hr] at hω'
  have hA : 0 ≤ 27 * C / (typ.volumeLower * ε) := by positivity
  have hpow : ((2 * r + 1 : ℕ) : ℝ) ^ (d - 6) ≤ (2 * (t : ℝ)) ^ (d - 6) :=
    pow_le_pow_left₀ hL0 hLt _
  have h1 : 27 * C / (typ.volumeLower * ε) * ((2 * r + 1 : ℕ) : ℝ) ^ (d - 6) ≤
      typ.countUpper * (2 * (t : ℝ)) ^ (d - 6) :=
    mul_le_mul hup hpow (pow_nonneg hL0 _) (hA.trans hup)
  exact (h1.trans hω'.le)

end NearCritical.Section10
