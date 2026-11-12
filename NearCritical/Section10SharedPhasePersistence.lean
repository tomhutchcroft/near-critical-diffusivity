module

public import NearCritical.Section10BridgeIntersectionLaw
public import NearCritical.Section10StepDiameter

/-! The nonterminal shared-step contraction in Step 4 of the pair estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- The event that some pair of representatives of the two nests can give
intersecting bridges, for fixed signs and a fixed pair of incoming nests. -/
def bridgeNestMeetEvent {d : ℕ} {ι ι' : Type*}
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (J' : Finset ι') (X : ι → Finset (Vertex d)) (Y : ι' → Finset (Vertex d)) :
    Set (Configuration d × Configuration d) :=
  {ξη | ∃ x ∈ J, ∃ y ∈ J',
    (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X x) B ∩
      section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty}

theorem measurableSet_bridgeNestMeetEvent {d : ℕ} {ι ι' : Type*}
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (J' : Finset ι') (X : ι → Finset (Vertex d)) (Y : ι' → Finset (Vertex d)) :
    MeasurableSet (bridgeNestMeetEvent E L R Q₁ F₁ Q₃ F₃ B J J' X Y) := by
  classical
  unfold bridgeNestMeetEvent
  have heq : {ξη : Configuration d × Configuration d | ∃ x ∈ J, ∃ y ∈ J',
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X x) B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty} =
      ⋃ xy ∈ J.product J', ⋃ z : Vertex d, {ξη |
        z ∈ section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X xy.1) B ∧
        z ∈ section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y xy.2) B} := by
    ext ξη
    constructor
    · rintro ⟨x, hx, y, hy, z, hz⟩
      exact Set.mem_iUnion.mpr ⟨(x, y), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩,
        Set.mem_iUnion.mpr ⟨z, Finset.mem_inter.mp hz⟩⟩⟩
    · intro h
      obtain ⟨xy, hxy⟩ := Set.mem_iUnion.mp h
      obtain ⟨hxy', hz⟩ := Set.mem_iUnion.mp hxy
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy'
      exact ⟨xy.1, hx, xy.2, hy, z, Finset.mem_inter.mpr hz⟩
  rw [heq]
  apply Finset.measurableSet_biUnion
  intro xy _
  apply MeasurableSet.iUnion
  intro z
  exact (measurableSet_section9_sprinkling_member E L R Q₁ F₁ Q₃ F₃ (X xy.1) B z).inter
    (measurableSet_section9_sprinkling_member E L R Q₁ F₁ Q₃ F₃ (Y xy.2) B z)

/-- With independent fair signs, two opposite-sign cases can continue a
nonterminal shared phase only when some pair of bridges meets. Bounding each
normalized success factor by 1 + ε/2 gives the source two-thirds contraction.
The sum divided by four is the conditional expectation over the fair signs. -/
theorem shared_phase_persistence_le {d : ℕ} {ι ι' : Type*}
    (μ : Measure (Configuration d × Configuration d)) [IsProbabilityMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (J' : Finset ι') (X : Bool → ι → Finset (Vertex d))
    (Y : Bool → ι' → Finset (Vertex d)) (w : Bool → Bool → Configuration d × Configuration d → ℝ)
    {ε k : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4)
    (hw : ∀ a b z, 0 ≤ w a b z ∧ w a b z ≤ (1+ε/2)^2)
    (hk : (J.card : ℝ) * (J'.card : ℝ) * k ≤ 1/40)
    (hpair : ∀ a b, a ≠ b → ∀ x ∈ J, ∀ y ∈ J', μ.real {ξη |
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X a x) B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y b y) B).Nonempty} ≤ k) :
    let A a b := if a = b then Set.univ else bridgeNestMeetEvent E L R Q₁ F₁ Q₃ F₃ B J J' (X a) (Y b)
    (∑ a : Bool, ∑ b : Bool, ∫ z, (A a b).indicator (w a b) z ∂μ) / 4 ≤ 2/3 := by
  intro A
  let R₀ := (1+ε/2)^2
  have hR₀ : 0 ≤ R₀ := sq_nonneg _
  have hmeas (a b : Bool) : MeasurableSet (A a b) := by
    by_cases hab : a = b
    · simpa only [A, if_pos hab] using (MeasurableSet.univ :
        MeasurableSet (Set.univ : Set (Configuration d × Configuration d)))
    · simpa only [A, if_neg hab] using
        measurableSet_bridgeNestMeetEvent E L R Q₁ F₁ Q₃ F₃ B J J' (X a) (Y b)
  have hmass (a b : Bool) : μ.real (A a b) ≤ if a = b then 1 else 1/40 := by
    by_cases hab : a = b
    · simp [A, hab, measureReal_def]
    · simpa only [A, if_neg hab, bridgeNestMeetEvent] using
        (bridge_intersection_probability_nests_le μ E L R Q₁ F₁ Q₃ F₃ B J J'
          (X a) (Y b) k (hpair a b hab)).trans hk
  have hweighted (a b : Bool) : (∫ z, (A a b).indicator (w a b) z ∂μ) ≤
      (if a = b then 1 else 1/40) * R₀ := by
    calc
      _ ≤ ∫ z, (A a b).indicator (fun _ => R₀) z ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
          ((integrable_const R₀).indicator (hmeas a b)) (Filter.Eventually.of_forall ?_)
        · intro z
          by_cases hz : z ∈ A a b <;> simp [hz, (hw a b z).1]
        · intro z
          by_cases hz : z ∈ A a b <;> simp [hz, R₀, (hw a b z).2]
      _ = μ.real (A a b) * R₀ := by rw [integral_indicator_const R₀ (hmeas a b), smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmass a b) hR₀
  have hρ₀ : 0 ≤ 1+ε/2 := by linarith
  have hρ : 1+ε/2 ≤ (9/8:ℝ) := by linarith
  have hR : R₀ ≤ (9/8:ℝ)^2 := (sq_le_sq₀ hρ₀ (by norm_num)).mpr hρ
  calc
    _ ≤ (∑ a : Bool, ∑ b : Bool, (if a = b then 1 else 1/40) * R₀) / 4 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => hweighted a b) (by norm_num)
    _ = (41/80:ℝ) * R₀ := by
      norm_num [Fintype.sum_bool] <;> ring
    _ ≤ (41/80:ℝ) * (9/8:ℝ)^2 := mul_le_mul_of_nonneg_left hR (by norm_num)
    _ ≤ _ := by norm_num

/-- The actual opposite regular patches on one marked face are separated
by at least one eighth of the mesh 2t, even for the same cluster. -/
theorem typicalRegularPatch_opposite_separation {d : ℕ} (hd : 2 ≤ d)
    (typ : TypicalParameters) (t : ℕ) (z : Vertex d) (ω : Configuration d)
    (C C' : Finset (Vertex d)) (face : Fin d × Bool) (a b : Bool) (hab : a ≠ b)
    {x y : Vertex d} (hx : x ∈ typicalRegularPatch typ t z ω C face a)
    (hy : y ∈ typicalRegularPatch typ t z ω C' face b) :
    (t : ℝ) / 4 ≤ latticeDistance x y := by
  let j₀ : Fin d := ⟨0, by omega⟩
  let j₁ : Fin d := ⟨1, by omega⟩
  have hne : j₀ ≠ j₁ := by
    intro he
    have hval := congrArg Fin.val he
    simp [j₀, j₁] at hval
  obtain ⟨j, hj⟩ : ∃ j : Fin d, j ≠ face.1 := by
    by_cases h : j₀ = face.1
    · exact ⟨j₁, fun he => hne (h.trans he.symm)⟩
    · exact ⟨j₀, h⟩
  have hsplit (u v : Vertex d) (hu : u ∈ typicalSplitFace t z face true)
      (hv : v ∈ typicalSplitFace t z face false) :
      (t : ℝ) / 4 ≤ latticeDistance u v := by
    have hu' := (Finset.mem_filter.mp hu).2 j hj
    have hv' := (Finset.mem_filter.mp hv).2 j hj
    simp at hu' hv'
    have hcoord := (le_abs_self ((u j : ℝ) - (v j : ℝ))).trans (latticeDistance_ge_coord u v j)
    linarith [hu'.1, hv'.2]
  have hx' := (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  have hy' := (Finset.mem_inter.mp (Finset.mem_filter.mp hy).1).2
  cases a <;> cases b
  · exact (hab rfl).elim
  · rw [latticeDistance_comm]
    exact hsplit y x hy' hx'
  · exact hsplit x y hx' hy'
  · exact (hab rfl).elim

/-- Separation of the sign patches and bounded nest size give the
two-thirds estimate at all sufficiently large source scales. -/
theorem shared_phase_persistence_of_separation {d : ℕ} {ι ι' : Type*}
    (hd : 7 ≤ d) (asymp : TwoPointAsymptotics d) (q₀ c : ℝ) (hc : 0 < c)
    (A₀ F₀ : ℝ) (κ : ℕ) :
    ∃ N : ℕ, ∀ (i : Fin d) (n : ℕ), 0 < n → N ≤ n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n:ℝ)^(-2:ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        (B.card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        ∀ (J : Finset ι) (J' : Finset ι') (X : Bool → ι → Finset (Vertex d))
          (Y : Bool → ι' → Finset (Vertex d)), J.card ≤ κ → J'.card ≤ κ →
        (∀ a x, x ∈ J → X a x ⊆ section9FiniteEndCube i n 0) →
        (∀ b y, y ∈ J' → Y b y ⊆ section9FiniteEndCube i n 0) →
        (∀ a x, x ∈ J → ((X a x).card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
        (∀ b y, y ∈ J' → ((Y b y).card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
        (∀ a b, a ≠ b → ∀ x ∈ J, ∀ y ∈ J', ∀ v ∈ X a x, ∀ z ∈ Y b y,
          c * (n:ℝ) ≤ latticeDistance v z) →
        ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1/4 →
        ∀ (w : Bool → Bool → Configuration d × Configuration d → ℝ),
          (∀ a b z, 0 ≤ w a b z ∧ w a b z ≤ (1+ε/2)^2) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        let A a b := if a = b then Set.univ else
          bridgeNestMeetEvent P L R Q₁ F₁ Q₃ F₃ B J J' (X a) (Y b)
        (∑ a : Bool, ∑ b : Bool, ∫ z, (A a b).indicator (w a b) z ∂μ) / 4 ≤ 2/3 := by
  obtain ⟨K, hK⟩ := bridge_intersection_probability_separated ((by decide : 5 ≤ 7).trans hd)
    asymp q₀ c hc A₀ F₀
  have hd' : (7:ℝ) ≤ d := by exact_mod_cast hd
  let D : ℝ := (κ:ℝ)^2 * max 0 K
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (40 * D)
  refine ⟨N, ?_⟩
  intro i n hn hNn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hR hB hBc
    J J' X Y hJ hJ' hX hY hXc hYc hsep ε hε hsmall w hw P μ A
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let k : ℝ := max 0 K * (n:ℝ)^(6-(d:ℝ))
  have hk₀ : 0 ≤ k := mul_nonneg (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
  have hcard : (J.card:ℝ) * (J'.card:ℝ) ≤ (κ:ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hJ) (by exact_mod_cast hJ')
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hk : (J.card:ℝ) * (J'.card:ℝ) * k ≤ 1/40 := by
    refine (mul_le_mul_of_nonneg_right hcard hk₀).trans ?_
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n from hn)
    have hnD : 40 * D ≤ (n:ℝ) :=
      hN.le.trans (by exact_mod_cast hNn)
    calc
      _ = D * (n:ℝ)^(6-(d:ℝ)) := by simp only [D, k, mul_assoc]
      _ ≤ D * (n:ℝ)^(-1:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hD
      _ = D / (n:ℝ) := by rw [Real.rpow_neg hn'.le, Real.rpow_one, div_eq_mul_inv]
      _ ≤ _ := (div_le_iff₀ hn').2 (by linarith)
  refine shared_phase_persistence_le μ P L R Q₁ F₁ Q₃ F₃ B J J' X Y w hε hsmall hw hk ?_
  intro a b hab x hx y hy
  refine (hK i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ (X a x) (Y b y) hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB (hX a x hx) (hY b y hy) (hsep a b hab x hx y hy) (hXc a x hx)
    (hYc b y hy) hBc).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

end NearCritical.Section10
