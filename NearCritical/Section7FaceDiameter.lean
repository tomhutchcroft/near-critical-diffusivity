module

public import NearCritical.Section7LowerWaterRaw

/-! Source proof of `lem.spanning.diam` (main.tex 1513-1556): the intrinsic
face diameter `rin` of a spanning component is at most `C2 n^2` with
conditional probability at least `1/2`.

Route. The source bounds `rin` by two longest self-avoiding paths from the root
to faces, obtained by a path surgery. Here only the triangle inequality at the
root is used: for face points `u, v` of the component of `x`,
`d(u,v) <= d(x,u) + d(x,v)`. So `rin > 2T` forces a face point at restricted
distance at least `T` from the root (`farFaceEvent`). The retained input
`FaceReachTail` is the weak first-moment bound
`P[some face point of C_n(x) is at distance >= T from x] <= K/T`,
which follows by Markov from the cited `eq.chemical_finite_moment`
((105) of CHS23), because a geodesic from `x` to a face point is a
self-avoiding open path from `x` to the bounding hyperplane.

Output: the conditional diameter input of `SpanningRawInputs`, hence
`prop.lower_water` from (A), the spanning/volume arm inputs and this tail.

 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section7
open MeasureTheory
open scoped Classical

/-- Real bound for the literal face diameter from bounds on all cross-face
pairs. Memberships are separated so no decidability instance is involved. -/
lemma spanningFaceDiameter_cast_le {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (C : Finset V) (faces : ι → Finset V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, i ≠ j → ∀ u ∈ C, u ∈ faces i → ∀ v ∈ C, v ∈ faces j →
      (G.dist u v : ℝ) ≤ B) :
    (spanningFaceDiameter G C faces : ℝ) ≤ B := by
  have hm : spanningFaceDiameter G C faces ≤ ⌊B⌋₊ := by
    unfold spanningFaceDiameter
    apply Finset.sup_le
    intro p hp
    apply Finset.sup_le
    intro xy hxy
    have hp' := (Finset.mem_filter.mp hp).2
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
    obtain ⟨a1, a2⟩ := Finset.mem_inter.mp h1
    obtain ⟨b1, b2⟩ := Finset.mem_inter.mp h2
    exact Nat.le_floor (h p.1 p.2 hp' xy.1 a1 a2 xy.2 b1 b2)
  calc (spanningFaceDiameter G C faces : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast hm
    _ ≤ B := Nat.floor_le hB

/-- Some point of the component of `x` on face `f` is at cube-restricted graph
distance at least `T` from `x`. -/
def farFaceEvent {d : ℕ} (N : ℕ) (x : Vertex d) (f : Fin d × Bool) (T : ℝ) :
    Set (Configuration d) :=
  {ω | ∃ u, u ∈ finiteBoxCluster ω (centeredBox d N) x ∧ u ∈ signedCubeFace d N f ∧
    T ≤ ((restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist x u : ℝ)}

/-- Weak first-moment input: consequence of the cited longest self-avoiding
path moment `eq.chemical_finite_moment` by Markov's inequality. -/
def FaceReachTail (d : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
    ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
      (percolation d (criticalPoint d)).real (farFaceEvent N x f T) ≤ K/T

/-- The remaining raw inputs (root region, two-sided spanning probability,
small-volume tail with the factor `1/8`). -/
def SpanningArmInputs (d : ℕ) : Prop :=
  ∃ (c Cs cz Cz : ℝ) (Z : ℕ → Finset (Vertex d)) (a : ℕ → ℝ) (N1 : ℕ),
    0 < c ∧ 0 ≤ Cs ∧ 0 < cz ∧ 0 ≤ Cz ∧
    ∀ N : ℕ, N1 ≤ N →
      Z N ⊆ centeredBox d N ∧
      cz*(N+1:ℝ)^d ≤ ((Z N).card:ℝ) ∧ ((Z N).card:ℝ) ≤ Cz*(N+1:ℝ)^d ∧
      (∀ x ∈ Z N, c/(N+1:ℝ)^2 ≤ (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x)) ∧
      (∀ x ∈ Z N, (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤ Cs/(N+1:ℝ)^2) ∧
      (∀ x ∈ Z N, (percolation d (criticalPoint d)).real
        ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card:ℝ) ≤ a N} ∩
          finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤
        (1/8)*(percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x))

/-- Triangle inequality at the root: if no face point of the component of `x`
is at distance `T` or more from `x`, its face diameter is at most `2T`. -/
theorem faceDiameter_of_not_far {d : ℕ} (ω : Configuration d) (N : ℕ) (x : Vertex d)
    {T : ℝ} (hT : 0 ≤ T) (hfar : ∀ f : Fin d × Bool, ω ∉ farFaceEvent N x f T) :
    rootedClusterProperty (centeredBox d N) x (FaceDiameterLE N (2*T)) ω := by
  change (spanningFaceDiameter
    (restrictedGraph ω (finiteBoxCluster ω (centeredBox d N) x : Set (Vertex d)))
    (finiteBoxCluster ω (centeredBox d N) x) (signedCubeFace d N) : ℝ) ≤ 2*T
  apply spanningFaceDiameter_cast_le _ _ _ (by linarith)
  intro f g _ u huC huf v hvC hvg
  have hux : ((restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist x u : ℝ) < T := by
    by_contra h
    exact hfar f ⟨u, huC, huf, not_lt.mp h⟩
  have hvx : ((restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist x v : ℝ) < T := by
    by_contra h
    exact hfar g ⟨v, hvC, hvg, not_lt.mp h⟩
  have hde := finiteBoxCluster_dist_eq ω (centeredBox d N) x huC hvC
  have hru : (restrictedGraph ω (centeredBox d N : Set (Vertex d))).Reachable x u :=
    ((mem_finiteBoxCluster ω (centeredBox d N) x u).mp huC).2
  have htri := hru.symm.dist_triangle_left v
  have hcomm : (restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist u x =
      (restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist x u := SimpleGraph.dist_comm
  rw [hcomm] at htri
  have htri' : ((restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist u v : ℝ) ≤
      ((restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist x u : ℝ) +
      ((restrictedGraph ω (centeredBox d N : Set (Vertex d))).dist x v : ℝ) := by
    exact_mod_cast htri
  rw [hde]
  linarith

/-- The conditional diameter step of `lem.spanning.diam`: for a root whose
spanning probability is at least `c/(N+1)^2`, the diameter bound
`rin <= C2 n^2` holds on at least half of the spanning event, once
`c C2 >= 16 d K`. -/
theorem half_spanning_le_diameter_and_spanning {d : ℕ} {K c C2 : ℝ} (hK : 0 ≤ K)
    (hC2 : 0 < C2) (hcC2 : 16*(d:ℝ)*K ≤ c*C2)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (farFaceEvent N x f T) ≤ K/T)
    (N : ℕ) (x : Vertex d) (hx : x ∈ centeredBox d N)
    (hspan : c/(N+1:ℝ)^2 ≤ (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x)) :
    (1/2)*(percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤
      (percolation d (criticalPoint d)).real
        ({ω | rootedClusterProperty (centeredBox d N) x
            (FaceDiameterLE N (C2 * (2*(N:ℝ)+1)^2)) ω} ∩
          finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) := by
  have hNn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hM : (0:ℝ) < ((N:ℝ)+1)^2 := by positivity
  have hn2 : ((N:ℝ)+1)^2 ≤ (2*(N:ℝ)+1)^2 := by nlinarith [hNn, mul_nonneg hNn hNn]
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = C2 * (2*(N:ℝ)+1)^2 / 2 := ⟨_, rfl⟩
  have hTpos : 0 < T := by
    rw [hTdef]
    have : 0 < C2 * (2*(N:ℝ)+1)^2 := mul_pos hC2 (lt_of_lt_of_le hM hn2)
    linarith
  have h2T : 2*T = C2 * (2*(N:ℝ)+1)^2 := by
    rw [hTdef]
    ring
  -- covering of the spanning event
  have hcover : finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x ⊆
      ({ω | rootedClusterProperty (centeredBox d N) x
          (FaceDiameterLE N (C2 * (2*(N:ℝ)+1)^2)) ω} ∩
        finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ∪
      ⋃ f ∈ (Finset.univ : Finset (Fin d × Bool)), farFaceEvent N x f T := by
    intro ω hω
    by_cases hfar : ∃ f : Fin d × Bool, ω ∈ farFaceEvent N x f T
    · obtain ⟨f, hf⟩ := hfar
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f, Finset.mem_univ f, hf⟩)
    · have hno : ∀ f : Fin d × Bool, ω ∉ farFaceEvent N x f T :=
        fun f hf => hfar ⟨f, hf⟩
      have hdiam := faceDiameter_of_not_far ω N x hTpos.le hno
      rw [h2T] at hdiam
      exact Or.inl ⟨hdiam, hω⟩
  have hfarsum : (percolation d (criticalPoint d)).real
      (⋃ f ∈ (Finset.univ : Finset (Fin d × Bool)), farFaceEvent N x f T) ≤
      2*(d:ℝ)*(K/T) := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun f _ => htail N x hx f T hTpos)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)
  have hmeas := le_trans (measureReal_mono (μ := percolation d (criticalPoint d)) hcover (measure_ne_top _ _)) (measureReal_union_le _ _)
  -- the far part is at most half of the spanning lower bound
  have hcT : 8*(d:ℝ)*K*((N:ℝ)+1)^2 ≤ c*T := by
    have h1 : c*T = (c*C2) * (2*(N:ℝ)+1)^2 / 2 := by
      rw [hTdef]
      ring
    have hdK : 0 ≤ 16*(d:ℝ)*K := by positivity
    have h2 : 16*(d:ℝ)*K*((N:ℝ)+1)^2 ≤ (c*C2)*(2*(N:ℝ)+1)^2 :=
      mul_le_mul hcC2 hn2 hM.le (le_trans hdK hcC2)
    rw [h1]
    linarith
  have hfarsmall : 2*(d:ℝ)*(K/T) ≤ (1/2)*(c/((N:ℝ)+1)^2) := by
    have e1 : 2*(d:ℝ)*(K/T) = (2*(d:ℝ)*K)/T := by ring
    have e2 : (1/2)*(c/((N:ℝ)+1)^2) = c/(2*((N:ℝ)+1)^2) := by
      rw [div_mul_div_comm, one_mul]
    have hnn : 0 ≤ (d:ℝ)*K*((N:ℝ)+1)^2 := by positivity
    rw [e1, e2, div_le_div_iff₀ hTpos (by positivity)]
    linarith [hcT, hnn]
  linarith

/-- The raw inputs of `SpanningRawInputs` from the arm/volume inputs and the
face-reach tail. -/
theorem spanningRawInputs_of_arm_and_tail {d : ℕ} (harm : SpanningArmInputs d)
    (htail : FaceReachTail d) : SpanningRawInputs d := by
  obtain ⟨c, Cs, cz, Cz, Z, a, N1, hc, hCs, hcz, hCz, hin⟩ := harm
  obtain ⟨K, hK, htailK⟩ := htail
  have hdK : 0 ≤ 16*(d:ℝ)*K := by positivity
  have hC2 : 0 < 16*(d:ℝ)*K/c + 1 := by positivity
  have hcC2 : 16*(d:ℝ)*K ≤ c*(16*(d:ℝ)*K/c + 1) := by
    have e : c*(16*(d:ℝ)*K/c + 1) = 16*(d:ℝ)*K*(c/c) + c := by ring
    rw [e, div_self hc.ne', mul_one]
    linarith
  refine ⟨1/2, c, Cs, cz, Cz, 16*(d:ℝ)*K/c + 1, Z, a, N1, by norm_num, hc, hCs, hcz, hCz,
    hC2, ?_⟩
  intro N hN
  obtain ⟨hZ, hlo, hhi, hsl, hsh, hlow⟩ := hin N hN
  refine ⟨hZ, hlo, hhi, hsl, hsh, ?_, ?_⟩
  · intro x hx
    exact half_spanning_le_diameter_and_spanning hK hC2 hcC2 htailK N x (hZ hx) (hsl x hx)
  · intro x hx
    have h := hlow x hx
    linarith

/-- **Source `prop.lower_water`, `eq.lower_water_general`**, from assumption (A),
`d >= 9`, the spanning/volume arm inputs and the face-reach tail. -/
theorem lower_water_general_of_arm_and_tail {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (harm : SpanningArmInputs d) (htail : FaceReachTail d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ r : ℕ, N0 ≤ r →
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) :=
  lower_water_general_of_raw_inputs hd i hA (spanningRawInputs_of_arm_and_tail harm htail)

/-- **Source `prop.lower_water`, `eq.lower_water`**, from the same inputs. -/
theorem lower_water_of_arm_and_tail {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (harm : SpanningArmInputs d) (htail : FaceReachTail d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ p : unitInterval, criticalPoint d < p →
      ∀ r : ℕ, N0 ≤ r → 2*r+1 ≤ chemicalCorrelationScale d p →
        c * ((p:ℝ) - (criticalPoint d : ℝ))^3 ≤
          annealedRelaxed (centeredBox d r) i (p:ℝ) :=
  lower_water_of_raw_inputs hd i hA (spanningRawInputs_of_arm_and_tail harm htail)

/-! ### Literal root region `Lambda_{n/16}` -/

/-- First display of source `lem.arm.2dspanning` (`eq.arm.2dspanning`) for the odd
cube `Lambda_n`, `n = 2N+1`, and roots in `Lambda_{n/16}` (here
`centeredBox d (N/16)`): the `2d`-spanning probability is of order `n^(-2)`. -/
def Arm2dSpanningStatement (d : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d (N/16) →
    c/(2*(N:ℝ)+1)^2 ≤ (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ∧
    (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤ C/(2*(N:ℝ)+1)^2

/-- Small-volume input (cited `eq.cluster_size`, with the cutoff `a N` of order
`lambda n^4` chosen so that the conditional probability is at most `1/8`). -/
def SpanningSmallVolumeInput (d : ℕ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d (N/16) →
    (percolation d (criticalPoint d)).real
      ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card:ℝ) ≤ a N} ∩
        finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤
      (1/8)*(percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x)

/-- The arm/volume inputs on the literal root region `Lambda_{n/16}`, whose
volume is of order `n^d` by an explicit count. -/
theorem spanningArmInputs_of_literal {d : ℕ} (harm : Arm2dSpanningStatement d)
    (hvol : SpanningSmallVolumeInput d) : SpanningArmInputs d := by
  obtain ⟨c, C, hc, hC, hspan⟩ := harm
  obtain ⟨a, hsmall⟩ := hvol
  have h16 : (0:ℝ) < 16^d := by positivity
  refine ⟨c/4, C, 1/16^d, 1, fun N => centeredBox d (N/16), a, 0, by linarith, hC,
    div_pos one_pos h16, zero_le_one, ?_⟩
  intro N _
  dsimp only
  have hNn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hM : (0:ℝ) < ((N:ℝ)+1)^2 := by positivity
  have hn : (0:ℝ) < (2*(N:ℝ)+1)^2 := by positivity
  have hn1 : ((N:ℝ)+1)^2 ≤ (2*(N:ℝ)+1)^2 := by nlinarith [hNn, mul_nonneg hNn hNn]
  have hn4 : (2*(N:ℝ)+1)^2 ≤ 4*((N:ℝ)+1)^2 := by nlinarith [hNn, mul_nonneg hNn hNn]
  have hnat1 : N + 1 ≤ 16*(2*(N/16)+1) := by omega
  have hnat2 : 2*(N/16)+1 ≤ N + 1 := by omega
  have hq0 : (0:ℝ) ≤ ((N:ℝ)+1)/16 := by positivity
  have hq1 : ((N:ℝ)+1)/16 ≤ 2*((N/16 : ℕ):ℝ)+1 := by
    have h : ((N:ℝ)+1) ≤ 16*(2*((N/16 : ℕ):ℝ)+1) := by exact_mod_cast hnat1
    linarith
  have hq2 : 2*((N/16 : ℕ):ℝ)+1 ≤ (N:ℝ)+1 := by exact_mod_cast hnat2
  have hq3 : (0:ℝ) ≤ 2*((N/16 : ℕ):ℝ)+1 := by positivity
  have hcard : ((centeredBox d (N/16)).card : ℝ) = (2*((N/16 : ℕ):ℝ)+1)^d := by
    rw [card_centeredBox_exact]
    first | (push_cast; ring) | push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    apply mem_centeredBox.mpr
    intro j
    have hj := (mem_centeredBox.mp hy) j
    have hle : ((N/16 : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.div_le_self N 16
    omega
  · rw [hcard]
    calc 1/16^d * ((N:ℝ)+1)^d = (((N:ℝ)+1)/16)^d := by
          rw [div_pow]
          ring
      _ ≤ (2*((N/16 : ℕ):ℝ)+1)^d := pow_le_pow_left₀ hq0 hq1 d
  · rw [hcard, one_mul]
    exact pow_le_pow_left₀ hq3 hq2 d
  · intro x hx
    refine le_trans ?_ (hspan N x hx).1
    rw [div_le_div_iff₀ hM hn]
    nlinarith [mul_le_mul_of_nonneg_left hn4 hc.le]
  · intro x hx
    refine le_trans (hspan N x hx).2 ?_
    exact div_le_div_of_nonneg_left hC hM hn1
  · intro x hx
    exact hsmall N x hx

/-- **Source `prop.lower_water`, `eq.lower_water_general`**, from assumption (A),
`d >= 9`, the literal `eq.arm.2dspanning`, the small-volume input and the
face-reach tail. -/
theorem lower_water_general_of_literal_inputs {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (harm : Arm2dSpanningStatement d)
    (hvol : SpanningSmallVolumeInput d) (htail : FaceReachTail d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ r : ℕ, N0 ≤ r →
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) :=
  lower_water_general_of_arm_and_tail hd i hA (spanningArmInputs_of_literal harm hvol) htail

/-- **Source `prop.lower_water`, `eq.lower_water`**, from the same inputs. -/
theorem lower_water_of_literal_inputs {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (harm : Arm2dSpanningStatement d)
    (hvol : SpanningSmallVolumeInput d) (htail : FaceReachTail d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ p : unitInterval, criticalPoint d < p →
      ∀ r : ℕ, N0 ≤ r → 2*r+1 ≤ chemicalCorrelationScale d p →
        c * ((p:ℝ) - (criticalPoint d : ℝ))^3 ≤
          annealedRelaxed (centeredBox d r) i (p:ℝ) :=
  lower_water_of_arm_and_tail hd i hA (spanningArmInputs_of_literal harm hvol) htail

end NearCritical.Section7
