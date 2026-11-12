module

public import NearCritical.Section7LowerWater
public import NearCritical.ClusterSpanningCountRate
public import NearCritical.ClusterWholeFamily
public import NearCritical.CriticalPointInterior

/-! Source Section 7, `prop.lower_water`, from the RAW Step-1 inputs of source
`prop.num_spanning_new` / `lem.spanning.diam` instead of `lem.spanning.diam`
itself.

The accepted lower-count rate `critical_spanningWindow_distinct_failure_rate`
(assumption (A), `d >= 9`) is applied to the component property "face diameter
at most `C2 n^2`" on the literal cube `centeredBox d N` with its `2d` signed
faces. The retained per-root inputs (`SpanningRawInputs`) are exactly:
* the `2d`-spanning probability of a root is of order `N^(-2)` (lower bound:
  source `lem.arm.2dspanning`, a paper lemma; upper bound: one-arm);
* conditionally on spanning, the face diameter is at most `C2 n^2` with
  probability at least `delta` (source proof of `lem.spanning.diam`, via the
  cited longest-path moment `eq.chemical_finite_moment`);
* the small-volume tail (cited `eq.cluster_size`);
* a root region of volume of order `N^d`.
Only the LOWER count is needed for Section 7, so the upper count of
`lem.spanning.diam` is not used.

 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section7
open MeasureTheory
open scoped Classical

/-- Component property: literal face diameter `rin` at most `K`. -/
def FaceDiameterLE {d : ℕ} (r : ℕ) (K : ℝ) (G : SimpleGraph (Vertex d))
    (C : Finset (Vertex d)) : Prop :=
  (spanningFaceDiameter G C (signedCubeFace d r) : ℝ) ≤ K

/-- Raw per-root inputs at the critical point for the cubes `centeredBox d N`,
`N >= N1`, in the exact form consumed by
`critical_spanningWindow_distinct_failure_rate`. -/
def SpanningRawInputs (d : ℕ) : Prop :=
  ∃ (δ c Cs cz Cz C2 : ℝ) (Z : ℕ → Finset (Vertex d)) (a : ℕ → ℝ) (N1 : ℕ),
    0 < δ ∧ 0 < c ∧ 0 ≤ Cs ∧ 0 < cz ∧ 0 ≤ Cz ∧ 0 < C2 ∧
    ∀ N : ℕ, N1 ≤ N →
      Z N ⊆ centeredBox d N ∧
      cz*(N+1:ℝ)^d ≤ ((Z N).card:ℝ) ∧ ((Z N).card:ℝ) ≤ Cz*(N+1:ℝ)^d ∧
      (∀ x ∈ Z N, c/(N+1:ℝ)^2 ≤ (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x)) ∧
      (∀ x ∈ Z N, (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤ Cs/(N+1:ℝ)^2) ∧
      (∀ x ∈ Z N, δ*(percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤
        (percolation d (criticalPoint d)).real
          ({ω | rootedClusterProperty (centeredBox d N) x
              (FaceDiameterLE N (C2 * (2*(N:ℝ)+1)^2)) ω} ∩
            finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x)) ∧
      (∀ x ∈ Z N, (percolation d (criticalPoint d)).real
        ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card:ℝ) ≤ a N} ∩
          finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x) ≤
        (δ/4)*(percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) (signedCubeFace d N) x))

/-- A spanning component with bounded face diameter is a short crossing in
every coordinate direction. The diameter is measured in the component's own
induced graph, and transferred to the cube-restricted graph. -/
theorem windowFamily_subset_crossingFamily {d : ℕ} (ω : Configuration d) (r : ℕ)
    (i : Fin d) (K a b : ℝ) :
    filteredClusterFamily ω (centeredBox d r)
        (fun C => spanningWindowProperty (signedCubeFace d r) (FaceDiameterLE r K) a b
          (restrictedGraph ω (C : Set (Vertex d))) C) ⊆
      crossingFamily ω r i K := by
  intro C hC
  simp only [filteredClusterFamily, Finset.mem_filter] at hC
  obtain ⟨hfam, hW⟩ := hC
  have hW' : FaceDiameterLE r K (restrictedGraph ω (C : Set (Vertex d))) C ∧
      (∀ f : Fin d × Bool, (C ∩ signedCubeFace d r f).Nonempty) ∧
      a < (C.card : ℝ) ∧ (C.card : ℝ) < b := hW
  obtain ⟨hP, hspan, _, _⟩ := hW'
  obtain ⟨x, hx⟩ := hspan (i, false)
  obtain ⟨y, hy⟩ := hspan (i, true)
  have hxC := (Finset.mem_inter.mp hx).1
  have hyC := (Finset.mem_inter.mp hy).1
  have hxi : x i = -(r:ℤ) := by
    have h := mem_signedCubeFace_coord (Finset.mem_inter.mp hx).2
    simpa using h
  have hyi : y i = (r:ℤ) := by
    have h := mem_signedCubeFace_coord (Finset.mem_inter.mp hy).2
    simpa using h
  have hne : ((i, false) : Fin d × Bool) ≠ (i, true) := by simp
  have hdist := dist_le_spanningFaceDiameter
    (restrictedGraph ω (C : Set (Vertex d))) C (signedCubeFace d r) hne hx hy
  have hrec : finiteBoxCluster ω (centeredBox d r) x = C :=
    finiteClusterFamily_recover ω (centeredBox d r) hfam hxC
  have hx' : x ∈ finiteBoxCluster ω (centeredBox d r) x := by
    rw [hrec]
    exact hxC
  have hy' : y ∈ finiteBoxCluster ω (centeredBox d r) x := by
    rw [hrec]
    exact hyC
  have hde := finiteBoxCluster_dist_eq ω (centeredBox d r) x hx' hy'
  rw [hrec] at hde
  have hPK : (spanningFaceDiameter (restrictedGraph ω (C : Set (Vertex d))) C
      (signedCubeFace d r) : ℝ) ≤ K := hP
  have hdistR : ((restrictedGraph ω (C : Set (Vertex d))).dist x y : ℝ) ≤ K :=
    le_trans (by exact_mod_cast hdist) hPK
  rw [hde] at hdistR
  exact (mem_crossingFamily ω r i K C).mpr ⟨hfam, x, hxC, y, hyC, hxi, hyi, hdistR⟩

/-- The crossing count of the odd cube from the raw inputs: with probability at
least `1/2`, at least `c1 n^(d-6)` components cross within `C2 n^2`. -/
theorem crossing_count_of_raw_inputs {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (hraw : SpanningRawInputs d) :
    ∃ c1 C2 : ℝ, 0 < c1 ∧ 0 < C2 ∧ ∃ N0 : ℕ, ∀ r : ℕ, N0 ≤ r →
      (1/2 : ℝ) ≤ (percolation d (criticalPoint d)).real
        {ω | c1 * (2*(r:ℝ)+1)^(d-6) ≤
          ((crossingFamily ω r i (C2 * (2*(r:ℝ)+1)^2)).card : ℝ)} := by
  obtain ⟨δ, c, Cs, cz, Cz, C2, Z, a, N1, hδ, hc, hCs, hcz, hCz, hC2, hin⟩ := hraw
  obtain ⟨C, D, hC, hD, hrate⟩ :=
    critical_spanningWindow_distinct_failure_rate hd hA δ c Cs cz Cz hδ hc hCs hcz hCz
  have ht : 0 < (δ*c*cz/4)/C := div_pos (by positivity) hC
  have h2pow : (0:ℝ) < 2^(d-6) := by positivity
  refine ⟨((δ*c*cz/4)/C)/2^(d-6), C2, div_pos ht h2pow, hC2, max N1 ⌈2*D⌉₊, ?_⟩
  intro r hr
  have hr1 : N1 ≤ r := le_trans (le_max_left _ _) hr
  have hr2 : ⌈2*D⌉₊ ≤ r := le_trans (le_max_right _ _) hr
  obtain ⟨hZ, hlo, hhi, hsl, hsh, hprop, hlow⟩ := hin r hr1
  have hfail := hrate r (Z r) hZ hlo hhi (Fin d × Bool) (signedCubeFace d r)
    (FaceDiameterLE r (C2 * (2*(r:ℝ)+1)^2)) (a r) hsl hsh hprop hlow
  have hsucc := wholePropertyFamily_success_ge_one_sub_failure (criticalPoint d)
    (centeredBox d r) (Z r) hZ
    (spanningWindowProperty (signedCubeFace d r)
      (FaceDiameterLE r (C2 * (2*(r:ℝ)+1)^2)) (a r) (C*(r+1:ℝ)^4))
    (((δ*c*cz/4)/C)*(r+1:ℝ)^(d-6))
  -- the failure probability is at most 1/2 for r >= 2D
  have hrpos : (0:ℝ) < (r:ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hr1' : (1:ℝ) ≤ (r:ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have h2D : 2*D ≤ (r:ℝ) := le_trans (Nat.le_ceil (2*D)) (by exact_mod_cast hr2)
  have hpow : (r:ℝ)+1 ≤ ((r:ℝ)+1)^(d-8) := le_self_pow₀ hr1' (by omega)
  have hXpos : (0:ℝ) < ((r:ℝ)+1)^(d-8) := pow_pos hrpos _
  have hsmall : D/((r:ℝ)+1)^(d-8) ≤ 1/2 := by
    rw [div_le_iff₀ hXpos]
    linarith
  have hfail' := le_trans hfail hsmall
  refine le_trans ?_ (le_trans hsucc (measureReal_mono ?_ (measure_ne_top _ _)))
  · linarith
  intro ω hω
  have hω' : ((δ*c*cz/4)/C)*(r+1:ℝ)^(d-6) ≤
      ((filteredClusterFamily ω (centeredBox d r)
        (fun Cc => spanningWindowProperty (signedCubeFace d r)
          (FaceDiameterLE r (C2 * (2*(r:ℝ)+1)^2)) (a r) (C*(r+1:ℝ)^4)
          (restrictedGraph ω (Cc : Set (Vertex d))) Cc)).card : ℝ) := hω
  have hsub := Finset.card_le_card (windowFamily_subset_crossingFamily ω r i
    (C2 * (2*(r:ℝ)+1)^2) (a r) (C*(r+1:ℝ)^4))
  have hsub' : ((filteredClusterFamily ω (centeredBox d r)
      (fun Cc => spanningWindowProperty (signedCubeFace d r)
        (FaceDiameterLE r (C2 * (2*(r:ℝ)+1)^2)) (a r) (C*(r+1:ℝ)^4)
        (restrictedGraph ω (Cc : Set (Vertex d))) Cc)).card : ℝ) ≤
      ((crossingFamily ω r i (C2 * (2*(r:ℝ)+1)^2)).card : ℝ) := by exact_mod_cast hsub
  -- scale comparison n = 2r+1 <= 2(r+1)
  have hn0 : (0:ℝ) ≤ 2*(r:ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hn2 : 2*(r:ℝ)+1 ≤ 2*((r:ℝ)+1) := by linarith
  have hpw : (2*(r:ℝ)+1)^(d-6) ≤ 2^(d-6) * ((r:ℝ)+1)^(d-6) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hn0 hn2 _
  have hscale : ((δ*c*cz/4)/C)/2^(d-6) * (2*(r:ℝ)+1)^(d-6) ≤
      ((δ*c*cz/4)/C)*((r:ℝ)+1)^(d-6) := by
    calc ((δ*c*cz/4)/C)/2^(d-6) * (2*(r:ℝ)+1)^(d-6)
        ≤ ((δ*c*cz/4)/C)/2^(d-6) * (2^(d-6) * ((r:ℝ)+1)^(d-6)) :=
          mul_le_mul_of_nonneg_left hpw (div_pos ht h2pow).le
      _ = ((δ*c*cz/4)/C) * ((2:ℝ)^(d-6)/2^(d-6)) * ((r:ℝ)+1)^(d-6) := by ring
      _ = ((δ*c*cz/4)/C)*((r:ℝ)+1)^(d-6) := by rw [div_self h2pow.ne', mul_one]
  exact le_trans hscale (le_trans hω' hsub')

/-- **Source `prop.lower_water`, `eq.lower_water_general`**, from assumption (A),
`d >= 9` and the raw spanning inputs: `c n^(-6) <= a(Lambda_n, p_c)` for the
relaxed annealed conductivity of the odd cubes, `n = 2r+1`, `r >= N_0`. -/
theorem lower_water_general_of_raw_inputs {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (hraw : SpanningRawInputs d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ r : ℕ, N0 ≤ r →
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := by
  have hpc := criticalPoint_pos_of_twoPointAsymptotics i hA
  obtain ⟨c1, C2, hc1, hC2, N0, hcount⟩ := crossing_count_of_raw_inputs hd i hA hraw
  have hC21 : 0 < 8*(C2+1) := by linarith
  refine ⟨(criticalPoint d : ℝ)^2 * c1 / (8*(C2+1)),
    div_pos (mul_pos (pow_pos hpc 2) hc1) hC21, N0, ?_⟩
  exact lower_water_of_crossing_count (by omega) i hc1 hC2 N0 hcount

/-- **Source `prop.lower_water`, `eq.lower_water`**, from the same inputs. -/
theorem lower_water_of_raw_inputs {d : ℕ} (hd : 9 ≤ d) (i : Fin d)
    (hA : TwoPointAsymptotics d) (hraw : SpanningRawInputs d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ p : unitInterval, criticalPoint d < p →
      ∀ r : ℕ, N0 ≤ r → 2*r+1 ≤ chemicalCorrelationScale d p →
        c * ((p:ℝ) - (criticalPoint d : ℝ))^3 ≤
          annealedRelaxed (centeredBox d r) i (p:ℝ) := by
  obtain ⟨c, hc, N0, hgen⟩ := lower_water_general_of_raw_inputs hd i hA hraw
  refine ⟨c, hc, N0, ?_⟩
  intro p hp r hr hscale
  have hNpos : (0:ℝ) < 2*(r:ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hle : (2*(r:ℝ)+1) ≤ (chemicalCorrelationScale d p : ℝ) := by exact_mod_cast hscale
  have h6 : (2*(r:ℝ)+1)^6 ≤ (chemicalCorrelationScale d p : ℝ)^6 :=
    pow_le_pow_left₀ hNpos.le hle 6
  have hinv := Section10.chemicalCorrelationScale_inverse_six_lower p hp
  have hinv2 : 1/(chemicalCorrelationScale d p : ℝ)^6 ≤ 1/(2*(r:ℝ)+1)^6 :=
    one_div_le_one_div_of_le (pow_pos hNpos 6) h6
  calc c * ((p:ℝ) - (criticalPoint d : ℝ))^3
      ≤ c * (1/(2*(r:ℝ)+1)^6) := mul_le_mul_of_nonneg_left (hinv.trans hinv2) hc.le
    _ = c / (2*(r:ℝ)+1)^6 := mul_one_div _ _
    _ ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := hgen r hr
    _ ≤ annealedRelaxed (centeredBox d r) i (p:ℝ) :=
        annealedRelaxed_parameter_mono _ i hp.le

end NearCritical.Section7
