module

public import NearCritical.PercolationEndpoints
public import NearCritical.ConductivityTranslation
public import NearCritical.Slab
public import NearCritical.ExternalExposureCost

/-! The local lattice star at a branch position consists of straight positive
coordinate rays. Their bonds and tips are explicit finite sets. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open scoped Classical

def starTip {d : ℕ} (b : Vertex d) (i : Fin d) (R : ℕ) : Vertex d :=
  b + coordinateRay i R

def rayBonds {d : ℕ} (b : Vertex d) (i : Fin d) (R : ℕ) : Finset (Bond d) :=
  (Finset.range R).image (fun k => (starTip b i k, i))

def starBonds {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) : Finset (Bond d) :=
  axes.biUnion (fun i => rayBonds b i R)

theorem coordinateRay_mem_centeredBox {d R k : ℕ} (i : Fin d) (hk : k ≤ R) :
    coordinateRay i k ∈ centeredBox d R := by
  apply mem_centeredBox.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp [coordinateRay, hk] <;> omega
  · simp [coordinateRay, hj]

theorem starTip_mem_box {d R k : ℕ} (b : Vertex d) (i : Fin d) (hk : k ≤ R) :
    starTip b i k ∈ translateSites b (centeredBox d R) :=
  (mem_translateSites _ _ _).mpr (coordinateRay_mem_centeredBox i hk)

theorem rayBond_tip {d : ℕ} (b : Vertex d) (i : Fin d) (k : ℕ) :
    bondTip (starTip b i k, i) = starTip b i (k + 1) := by
  change bondTip (translateBond b (coordinateRay i k, i)) = b + coordinateRay i (k + 1)
  rw [bondTip_translate, bondTip_coordinateRay]

theorem rayBonds_card {d : ℕ} (b : Vertex d) (i : Fin d) (R : ℕ) :
    (rayBonds b i R).card = R := by
  unfold rayBonds
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro k l h
  have he : starTip b i k = starTip b i l := congrArg Prod.fst h
  exact coordinateRay_injective i (add_left_cancel he)

theorem rayBonds_disjoint {d : ℕ} (b : Vertex d) {i j : Fin d} (hij : i ≠ j) (R : ℕ) :
    Disjoint (rayBonds b i R) (rayBonds b j R) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp he'
  exact hij (congrArg Prod.snd hl).symm

theorem starBonds_card {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    (starBonds b axes R).card = axes.card * R := by
  unfold starBonds
  rw [Finset.card_biUnion]
  · simp [rayBonds_card]
  · intro i _ j _ hij
    exact rayBonds_disjoint b hij R

/-- Different positive coordinate rays only meet at their common root. -/
theorem starTip_distinct_rays {d : ℕ} (b : Vertex d) {i j : Fin d} (hij : i ≠ j)
    {k l : ℕ} (hk : 0 < k) : starTip b i k ≠ starTip b j l := by
  intro h
  have he := congrFun h i
  have hzero : (k : ℤ) = 0 := by
    simpa [starTip, coordinateRay, Pi.add_apply, hij] using he
  omega

/-- The tips of two rays of length `R` are separated by at least `R`. -/
theorem starTips_dist {d : ℕ} (b : Vertex d) {i j : Fin d} (hij : i ≠ j) (R : ℕ) :
    (R : ℝ) ≤ dist (starTip b i R) (starTip b j R) := by
  refine le_trans ?_ (dist_le_pi_dist (starTip b i R) (starTip b j R) i)
  rw [Int.dist_eq]
  simp [starTip, coordinateRay, Pi.add_apply, hij, Int.cast_add, abs_of_nonneg]

theorem ray_reachable_restricted {d : ℕ} (ω : Configuration d) (D : Set (Vertex d))
    (b : Vertex d) (i : Fin d) (R : ℕ)
    (hD : (translateSites b (centeredBox d R) : Set (Vertex d)) ⊆ D)
    (hopen : ∀ e ∈ rayBonds b i R, ω e = true) :
    (restrictedGraph ω D).Reachable b (starTip b i R) := by
  have hwalk : ∀ k ≤ R, (restrictedGraph ω D).Reachable b (starTip b i k) := by
    intro k
    induction k with
    | zero =>
        intro _
        have hz : coordinateRay i 0 = (0 : Vertex d) := by
          ext j
          by_cases hj : j = i <;> simp [coordinateRay, hj]
        simp [starTip, hz]
    | succ k ih =>
        intro hk
        have hstep : (restrictedGraph ω D).Adj (starTip b i k) (starTip b i (k + 1)) := by
          have he : (starTip b i k, i) ∈ rayBonds b i R :=
            Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
          refine ⟨⟨(starTip b i k, i), hopen _ he, Or.inl ⟨rfl, (rayBond_tip b i k).symm⟩⟩, ?_, ?_⟩
          · exact hD (starTip_mem_box b i (by omega))
          · exact hD (starTip_mem_box b i hk)
        exact (ih (by omega)).trans hstep.reachable
  exact hwalk R le_rfl

theorem star_reachable_restricted {d : ℕ} (ω : Configuration d) (D : Set (Vertex d))
    (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ)
    (hD : (translateSites b (centeredBox d R) : Set (Vertex d)) ⊆ D)
    (hopen : ∀ e ∈ starBonds b axes R, ω e = true) (i : Fin d) (hi : i ∈ axes) :
    (restrictedGraph ω D).Reachable b (starTip b i R) :=
  ray_reachable_restricted ω D b i R hD
    (fun e he => hopen e (Finset.mem_biUnion.mpr ⟨i, hi, he⟩))

/-- The bases of the positive star bonds are exactly the ray vertices
before their tips. -/
def starNonTipVertices {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    Finset (Vertex d) :=
  (starBonds b axes R).image Prod.fst

theorem starTip_not_mem_nonTip {d : ℕ} (b : Vertex d) (axes : Finset (Fin d))
    (i : Fin d) {R : ℕ} (hR : 0 < R) :
    starTip b i R ∉ starNonTipVertices b axes R := by
  intro h
  obtain ⟨e, he, htip⟩ := Finset.mem_image.mp h
  obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp he
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hej
  have hkR := Finset.mem_range.mp hk
  by_cases hij : i = j
  · subst j
    have hEq := coordinateRay_injective i (add_left_cancel htip)
    omega
  · exact starTip_distinct_rays b hij hR htip.symm

/-- The incident bonds at which a star pattern prescribes open or closed
states. The exit balls add a separate finite set of prescribed bonds. -/
def starGuardBonds {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    Finset (Bond d) :=
  (starNonTipVertices b axes R).biUnion External.vertexIncidentBonds

theorem starBonds_subset_guard {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    starBonds b axes R ⊆ starGuardBonds b axes R := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image.mpr ⟨e, he, rfl⟩,
    (External.mem_vertexIncidentBonds _ _).mpr (Or.inl rfl)⟩

theorem starGuardBonds_card_le {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    (starGuardBonds b axes R).card ≤ axes.card * R * (2 * d) := by
  unfold starGuardBonds
  calc
    _ ≤ ∑ v ∈ starNonTipVertices b axes R, (External.vertexIncidentBonds v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ starNonTipVertices b axes R, 2 * d :=
      Finset.sum_le_sum (fun v _ => External.card_vertexIncidentBonds_le v)
    _ = (starNonTipVertices b axes R).card * (2 * d) := by simp
    _ ≤ axes.card * R * (2 * d) := by
      apply Nat.mul_le_mul_right
      rw [← starBonds_card b axes R]
      exact Finset.card_image_le

/-- A configuration realizes the star pattern if the star bonds are the
only open bonds in its guard. -/
def starPattern {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    Set (Configuration d) :=
  {ω | ∀ e ∈ starGuardBonds b axes R, ω e = decide (e ∈ starBonds b axes R)}

theorem starPattern_open {d : ℕ} {b : Vertex d} {axes : Finset (Fin d)} {R : ℕ}
    {ω : Configuration d} (hω : ω ∈ starPattern b axes R) :
    ∀ e ∈ starBonds b axes R, ω e = true := by
  intro e he
  have hh := hω e (starBonds_subset_guard b axes R he)
  simpa [he] using hh

/-- No open bond incident to a non-tip vertex can leave a realized star
except along one of the prescribed rays. -/
theorem starPattern_incident_open {d : ℕ} {b : Vertex d} {axes : Finset (Fin d)} {R : ℕ}
    {ω : Configuration d} (hω : ω ∈ starPattern b axes R) {e : Bond d} (he : ω e = true)
    (hinc : e.1 ∈ starNonTipVertices b axes R ∨ bondTip e ∈ starNonTipVertices b axes R) :
    e ∈ starBonds b axes R := by
  have hguard : e ∈ starGuardBonds b axes R := by
    rcases hinc with hb | ht
    · exact Finset.mem_biUnion.mpr ⟨e.1, hb,
        (External.mem_vertexIncidentBonds _ _).mpr (Or.inl rfl)⟩
    · exact Finset.mem_biUnion.mpr ⟨bondTip e, ht,
        (External.mem_vertexIncidentBonds _ _).mpr (Or.inr rfl)⟩
  have hh := hω e hguard
  rw [he] at hh
  exact of_decide_eq_true hh.symm

end NearCritical.SplitCrossDirect
