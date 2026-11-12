module

public import NearCritical.CriticalTriangle

/-! The new spatial three-point deduction of source `lem.threepoint_upper`.
The standard BK tree-graph and spatial bubble estimates remain named inputs;
this module proves their new min/max-separation consequence on actual events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Source |x-y|: supremum distance of the real coordinate embeddings. -/
def latticeDistance {d : ℕ} (x y : Vertex d) : ℝ := dist (vertexReal x) (vertexReal y)

lemma latticeDistance_comm {d : ℕ} (x y : Vertex d) :
    latticeDistance x y = latticeDistance y x := dist_comm _ _

lemma latticeDistance_nonneg {d : ℕ} (x y : Vertex d) : 0 ≤ latticeDistance x y := dist_nonneg

lemma latticeDistance_triangle {d : ℕ} (x y z : Vertex d) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := dist_triangle _ _ _

lemma latticeDistance_pos {d : ℕ} {x y : Vertex d} (h : x ≠ y) :
    0 < latticeDistance x y := by
  apply dist_pos.mpr
  exact fun heq => h (vertexReal_injective d heq)

lemma latticeDistance_le_euclidean {d : ℕ} (x y : Vertex d) :
    latticeDistance x y ≤ euclideanNorm (x - y) := by
  have he : vertexReal (x - y) = vertexReal x - vertexReal y := by
    funext i
    change ((x i - y i : ℤ) : ℝ) = (x i : ℝ) - (y i : ℝ)
    exact Int.cast_sub _ _
  simpa only [latticeDistance, dist_eq_norm, he] using
    vertexReal_norm_le_euclideanNorm (x - y)

/-- Positive coefficient in the regularized global Green upper estimate. -/
def CriticalSupGreenUpper (d : ℕ) (G : ℝ) : Prop :=
  ∀ x y : Vertex d, twoPoint d (criticalPoint d) x y ≤
    G * (max 1 (latticeDistance x y)) ^ ((2 : ℝ) - (d : ℝ))

/-- Named STANDARD input: spatial bubble estimate used in the proof of
lem.threepoint_upper. Summability is explicit, so real tsum cannot hide divergence. -/
def CriticalSpatialBubbleInput (d : ℕ) (B : ℝ) : Prop :=
  ∀ x y : Vertex d,
    Summable (fun u : Vertex d => twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y) ∧
    (∑' u : Vertex d, twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y) ≤
      B * (max 1 (latticeDistance x y)) ^ ((4 : ℝ) - (d : ℝ))

/-- Named STANDARD input: BK tree-graph/branch-point inequality from the
first displayed step of the source proof. The desired min/max bound is absent. -/
def ThreePointTreeGraphInput (d : ℕ) : Prop :=
  ∀ x y z : Vertex d,
    (percolation d (criticalPoint d)).real (connectionEvent x y ∩ connectionEvent x z) ≤
      ∑' u : Vertex d, twoPoint d (criticalPoint d) u x *
        twoPoint d (criticalPoint d) u y * twoPoint d (criticalPoint d) u z

def tripleMinSeparation {d : ℕ} (x y z : Vertex d) : ℝ :=
  min (latticeDistance x y) (min (latticeDistance y z) (latticeDistance x z))

def tripleMaxSeparation {d : ℕ} (x y z : Vertex d) : ℝ :=
  max (latticeDistance x y) (max (latticeDistance y z) (latticeDistance x z))

lemma tripleMinSeparation_pos {d : ℕ} {x y z : Vertex d}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    0 < tripleMinSeparation x y z := by
  exact lt_min (latticeDistance_pos hxy) (lt_min (latticeDistance_pos hyz) (latticeDistance_pos hxz))

/-- Every branch point is far from at least one endpoint, at half the maximal
pair separation. This avoids assuming a nearest-region decomposition. -/
lemma branchPoint_far_endpoint {d : ℕ} (x y z u : Vertex d) :
    tripleMaxSeparation x y z / 2 ≤ latticeDistance u x ∨
    tripleMaxSeparation x y z / 2 ≤ latticeDistance u y ∨
    tripleMaxSeparation x y z / 2 ≤ latticeDistance u z := by
  by_contra! h
  have hxy := latticeDistance_triangle x u y
  have hyz := latticeDistance_triangle y u z
  have hxz := latticeDistance_triangle x u z
  rw [latticeDistance_comm x u] at hxy hxz
  rw [latticeDistance_comm y u] at hyz
  have h1 : latticeDistance x y < tripleMaxSeparation x y z := by linarith
  have h2 : latticeDistance y z < tripleMaxSeparation x y z := by linarith
  have h3 : latticeDistance x z < tripleMaxSeparation x y z := by linarith
  have hm := max_lt h1 (max_lt h2 h3)
  exact (lt_irrefl _ hm)

/-- The actual source assumption already gives the needed regularized Green
bound in the source supremum distance; this is not an additional literature input. -/
theorem criticalSupGreenUpper_of_asymptotics {d : ℕ} (hd : 2 ≤ d) (h : TwoPointAsymptotics d) :
    ∃ G : ℝ, 0 < G ∧ CriticalSupGreenUpper d G := by
  obtain ⟨G, hG, hb⟩ := critical_twoPoint_global_upper hd h
  refine ⟨G, hG, ?_⟩
  intro x y
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact (hb x y).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity)
      (max_le_max_left 1 (latticeDistance_le_euclidean x y)) (sub_nonpos.mpr hd')) hG.le)

/-- NEW source deduction: the branch-point diagram has the exact min/max
power decay, conditional on the named standard spatial bubble estimate. -/
theorem threePointDiagram_upper {d : ℕ} (hd : 4 < d)
    {G B : ℝ} (hG : 0 < G) (hB : 0 < B)
    (green : CriticalSupGreenUpper d G) (bubble : CriticalSpatialBubbleInput d B)
    {x y z : Vertex d} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (∑' u : Vertex d, twoPoint d (criticalPoint d) u x *
      twoPoint d (criticalPoint d) u y * twoPoint d (criticalPoint d) u z) ≤
      (3 * G * B * (2 : ℝ) ^ ((d : ℝ) - 2)) *
        tripleMinSeparation x y z ^ ((4 : ℝ) - (d : ℝ)) *
        tripleMaxSeparation x y z ^ ((2 : ℝ) - (d : ℝ)) := by
  let a := tripleMinSeparation x y z
  let M := tripleMaxSeparation x y z
  let e : ℝ := 2 - (d : ℝ)
  let f : ℝ := 4 - (d : ℝ)
  have ha : 0 < a := tripleMinSeparation_pos hxy hyz hxz
  have hM : 0 < M := (latticeDistance_pos hxy).trans_le (le_max_left _ _)
  have hd' : (4 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have he : e ≤ 0 := by dsimp [e]; linarith
  have hf : f ≤ 0 := by dsimp [f]; linarith
  let L := G * (M / 2) ^ e
  have hL : 0 ≤ L := mul_nonneg hG.le (Real.rpow_nonneg (by positivity) _)
  have hfar : ∀ u v : Vertex d, M / 2 ≤ latticeDistance u v →
      twoPoint d (criticalPoint d) u v ≤ L := by
    intro u v huv
    exact (green u v).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity)
        (huv.trans (le_max_right _ _)) he) hG.le)
  have hs1 := (bubble x y).1
  have hs2 := (bubble y z).1
  have hs3 := (bubble x z).1
  have hs := ((hs1.add hs2).add hs3).mul_left L
  have hpoint : ∀ u : Vertex d,
      twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y *
        twoPoint d (criticalPoint d) u z ≤
      L * (twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y +
        twoPoint d (criticalPoint d) u y * twoPoint d (criticalPoint d) u z +
        twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u z) := by
    intro u
    have ha0 := twoPoint_nonneg (criticalPoint d) u x
    have hb0 := twoPoint_nonneg (criticalPoint d) u y
    have hc0 := twoPoint_nonneg (criticalPoint d) u z
    rcases branchPoint_far_endpoint x y z u with h | h | h
    · have hl := hfar u x h
      have hm := mul_le_mul_of_nonneg_right hl (mul_nonneg hb0 hc0)
      nlinarith [mul_nonneg hL (mul_nonneg ha0 hb0), mul_nonneg hL (mul_nonneg ha0 hc0)]
    · have hl := hfar u y h
      have hm := mul_le_mul_of_nonneg_right hl (mul_nonneg ha0 hc0)
      nlinarith [mul_nonneg hL (mul_nonneg ha0 hb0), mul_nonneg hL (mul_nonneg hb0 hc0)]
    · have hl := hfar u z h
      have hm := mul_le_mul_of_nonneg_right hl (mul_nonneg ha0 hb0)
      nlinarith [mul_nonneg hL (mul_nonneg hb0 hc0), mul_nonneg hL (mul_nonneg ha0 hc0)]
  have ht := hs.of_nonneg_of_le (fun u => mul_nonneg
    (mul_nonneg (twoPoint_nonneg _ _ _) (twoPoint_nonneg _ _ _)) (twoPoint_nonneg _ _ _)) hpoint
  have hb1 : (∑' u : Vertex d, twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y) ≤ B * a ^ f := by
    exact (bubble x y).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha
        ((min_le_left _ _).trans (le_max_right _ _)) hf) hB.le)
  have hb2 : (∑' u : Vertex d, twoPoint d (criticalPoint d) u y * twoPoint d (criticalPoint d) u z) ≤ B * a ^ f := by
    exact (bubble y z).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha
        ((min_le_right _ _).trans ((min_le_left _ _).trans (le_max_right _ _))) hf) hB.le)
  have hb3 : (∑' u : Vertex d, twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u z) ≤ B * a ^ f := by
    exact (bubble x z).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha
        ((min_le_right _ _).trans ((min_le_right _ _).trans (le_max_right _ _))) hf) hB.le)
  calc
    _ ≤ ∑' u : Vertex d, L * (twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y +
        twoPoint d (criticalPoint d) u y * twoPoint d (criticalPoint d) u z +
        twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u z) :=
      ht.tsum_le_tsum hpoint hs
    _ = L * ((∑' u, twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y) +
        (∑' u, twoPoint d (criticalPoint d) u y * twoPoint d (criticalPoint d) u z) +
        (∑' u, twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u z)) := by
      rw [((hs1.add hs2).add hs3).tsum_mul_left L, (hs1.add hs2).tsum_add hs3, hs1.tsum_add hs2]
    _ ≤ L * (3 * (B * a ^ f)) := mul_le_mul_of_nonneg_left (by linarith) hL
    _ = _ := by
      dsimp [L, e, f, a, M]
      rw [Real.div_rpow hM.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have heq : -((2 : ℝ) - (d : ℝ)) = (d : ℝ) - 2 := by ring
      rw [heq]
      ring

/-- Source lem.threepoint_upper as a new deduction on actual percolation
probabilities, with the two standard literature inputs disclosed. -/
theorem threePoint_probability_upper_of_standard_inputs {d : ℕ} (hd : 4 < d)
    {G B : ℝ} (hG : 0 < G) (hB : 0 < B)
    (green : CriticalSupGreenUpper d G) (bubble : CriticalSpatialBubbleInput d B)
    (tree : ThreePointTreeGraphInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : Vertex d, x ≠ y → y ≠ z → x ≠ z →
      (percolation d (criticalPoint d)).real (connectionEvent x y ∩ connectionEvent x z) ≤
        C * tripleMinSeparation x y z ^ ((4 : ℝ) - (d : ℝ)) *
          tripleMaxSeparation x y z ^ ((2 : ℝ) - (d : ℝ)) := by
  refine ⟨3 * G * B * (2 : ℝ) ^ ((d : ℝ) - 2), by positivity, ?_⟩
  intro x y z hxy hyz hxz
  exact (tree x y z).trans (threePointDiagram_upper hd hG hB green bubble hxy hyz hxz)

/-- Version using the existing exact source assumption (A), with standard
bubble/tree-graph inputs still explicit rather than asserted as proved. -/
theorem threePoint_probability_upper_of_asymptotics_and_standard_inputs {d : ℕ}
    (hd : 4 < d) (h : TwoPointAsymptotics d) {B : ℝ} (hB : 0 < B)
    (bubble : CriticalSpatialBubbleInput d B) (tree : ThreePointTreeGraphInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : Vertex d, x ≠ y → y ≠ z → x ≠ z →
      (percolation d (criticalPoint d)).real (connectionEvent x y ∩ connectionEvent x z) ≤
        C * tripleMinSeparation x y z ^ ((4 : ℝ) - (d : ℝ)) *
          tripleMaxSeparation x y z ^ ((2 : ℝ) - (d : ℝ)) := by
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics (by omega) h
  exact threePoint_probability_upper_of_standard_inputs hd hG hB green bubble tree

end NearCritical
