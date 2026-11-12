module
public import NearCritical.Section9CoalescenceBubble
public import NearCritical.Section9CoalescenceMass

/-! Candidate bubbles retain the genuine adjacent tail/head geometry. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Every actual nearest-neighbor lattice adjacency has supremum distance
at most one, independently of the bond state. -/
theorem section9_adjacent_lattice_distance_le_one {d : ℕ} {x y : Vertex d}
    (hxy : (openGraph (fun _ : Bond d => true)).Adj x y) :
    latticeDistance x y ≤ 1 := by
  have htip (b : Bond d) : latticeDistance (bondTip b) b.1 ≤ 1 := by
    change dist (vertexReal (bondTip b)) (vertexReal b.1) ≤ 1
    apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    change dist ((bondTip b i : ℤ) : ℝ) ((b.1 i : ℤ) : ℝ) ≤ 1
    rw [Real.dist_eq]
    by_cases hi : i = b.2
    · subst i
      simp [bondTip]
    · simp [bondTip,Function.update_of_ne hi]
  obtain ⟨b,_,h | h⟩ := hxy
  · obtain ⟨rfl,rfl⟩ := h
    rw [latticeDistance_comm]
    exact htip b
  · obtain ⟨rfl,rfl⟩ := h
    exact htip b

/-- Moving one endpoint across one physical lattice bond costs at most
2^(d-2) in the regularized second-order kernel. -/
theorem section9_green_kernel_neighbor_shift {d : ℕ} (hd : 2 ≤ d)
    (v x y : Vertex d) (hxy : (openGraph (fun _ : Bond d => true)).Adj x y) :
    (max 1 (latticeDistance v y))^((2 : ℝ)-(d : ℝ)) ≤
      (2 : ℝ)^((d : ℝ)-2)*(max 1 (latticeDistance v x))^((2 : ℝ)-(d : ℝ)) := by
  let a : ℝ := 2-(d : ℝ)
  let A : ℝ := max 1 (latticeDistance v x)
  let B : ℝ := max 1 (latticeDistance v y)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hstep : latticeDistance y x ≤ 1 := section9_adjacent_lattice_distance_le_one hxy.symm
  have hAB : A ≤ 2*B := by
    apply max_le
    · linarith
    · have ht := latticeDistance_triangle v y x
      have hdist : latticeDistance v y ≤ B := le_max_right _ _
      linarith
  have ha : a ≤ 0 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [a]
    linarith
  have hscale : (A/2)^a = (2 : ℝ)^((d : ℝ)-2)*A^a := by
    have he : (d : ℝ)-2 = -a := by dsimp [a]; ring
    rw [he,Real.div_rpow hA.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a]
    ring
  exact (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < A/2)
    (by linarith : A/2 ≤ B) ha).trans_eq hscale

/-- A finite candidate bubble uses each genuine tail/head pair, not two
copies of one endpoint. The bound is uniform in the candidate cutoff. -/
theorem section9_candidate_bubble_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (S : Finset (Vertex d)) (u v : Vertex d) :
    ∑ e ∈ orientedLatticePairs S,
      twoPoint d (criticalPoint d) u e.1 * twoPoint d (criticalPoint d) v e.2 ≤
      ((2*(d : ℝ))*(2 : ℝ)^((d : ℝ)-2)*G^2 *
        ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))) *
        (max 1 (latticeDistance u v))^((4 : ℝ)-(d : ℝ)) := by
  let a : ℝ := 2-(d : ℝ)
  let C : ℝ := G^2*(2 : ℝ)^((d : ℝ)-2)
  let K : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let F := fun z : Vertex d => (max 1 (latticeDistance u z))^a * (max 1 (latticeDistance v z))^a
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have hF (z : Vertex d) : 0 ≤ F z := mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hpoint (e : Vertex d × Vertex d) (he : e ∈ orientedLatticePairs S) :
      twoPoint d (criticalPoint d) u e.1 * twoPoint d (criticalPoint d) v e.2 ≤ C*F e.1 := by
    have hadj := ((mem_orientedLatticePairs S e.1 e.2).mp he).2.2
    have hshift := section9_green_kernel_neighbor_shift (by omega : 2 ≤ d) v e.1 e.2 hadj
    calc
      _ ≤ (G*(max 1 (latticeDistance u e.1))^a) *
          (G*((2 : ℝ)^((d : ℝ)-2)*(max 1 (latticeDistance v e.1))^a)) :=
        mul_le_mul (green u e.1) ((green v e.2).trans
          (mul_le_mul_of_nonneg_left hshift hG)) measureReal_nonneg
          (mul_nonneg hG (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
      _ = _ := by dsimp [C,F]; ring
  have hswap (e : Vertex d × Vertex d) (he : e ∈ orientedLatticePairs S) : e.swap ∈ orientedLatticePairs S := by
    obtain ⟨h₁,h₂,hadj⟩ := (mem_orientedLatticePairs S e.1 e.2).mp he
    exact (mem_orientedLatticePairs S e.2 e.1).mpr ⟨h₂,h₁,hadj.symm⟩
  have htail : (∑ e ∈ orientedLatticePairs S, F e.1) ≤ (2*(d : ℝ))*∑ z ∈ S, F z := by
    calc
      _ = ∑ e ∈ orientedLatticePairs S, F e.2 := by
        apply Finset.sum_bij (fun e _ => e.swap)
        · exact hswap
        · intro x _ y _ hxy
          exact congrArg Prod.swap hxy
        · intro e he
          exact ⟨e.swap,hswap e he,rfl⟩
        · intro e _
          rfl
      _ ≤ _ := section9_oriented_head_mass_le S F (fun z _ => hF z)
  have hconv : (∑ z ∈ S, F z) ≤
      K*(max 1 (latticeDistance u v))^((4 : ℝ)-(d : ℝ)) := by
    simpa only [F,a,K,Nat.cast_one] using Section8.truncated_green_convolution_le hd 1 (by decide) S u v

  calc
    _ ≤ ∑ e ∈ orientedLatticePairs S, C*F e.1 := Finset.sum_le_sum hpoint
    _ = C*(∑ e ∈ orientedLatticePairs S, F e.1) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*((2*(d : ℝ))*∑ z ∈ S, F z) := mul_le_mul_of_nonneg_left htail hC
    _ ≤ C*((2*(d : ℝ)) * (K*(max 1 (latticeDistance u v))^((4 : ℝ)-(d : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv (by positivity)) hC
    _ = _ := by dsimp [C,K]; ring

end NearCritical
