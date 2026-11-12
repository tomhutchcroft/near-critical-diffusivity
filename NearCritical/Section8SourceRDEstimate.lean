module
public import NearCritical.Section8PositiveRD
public import NearCritical.Section8RDGapOne
public import NearCritical.Section8AnnulusInversion
public import NearCritical.Section8SourceRDChart
public import NearCritical.Section8SourceAnnulusBridge
public import NearCritical.AppendixTwoPointBridge

/-! Signed RD estimate on the actual integer-radius source annulus. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory AppendixVariance
open scoped Classical

private theorem distance_zero_neg {d : ℕ} (x : Vertex d) :
    latticeDistance 0 (-x) = latticeDistance 0 x := by
  have hz : vertexReal (0 : Vertex d) = (0 : Fin d → ℝ) := by
    ext i
    simp [vertexReal]
  have hn : vertexReal (-x) = -vertexReal x := by
    ext i
    simp [vertexReal]
  unfold latticeDistance
  rw [hz,hn]
  simpa only [neg_zero] using dist_neg_neg (0 : Fin d → ℝ) (vertexReal x)

/-- A uniform positive coefficient for all dominant signs and all positive RD
gaps. The annulus and RD set are the literal natural-radius Appendix objects.
The cited half-space and slab estimates remain explicit inputs. -/
theorem source_RD_connection_upper {k : ℕ} (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (k+1) C)
    (arm : ∀ j : Fin (k+1), HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin (k+1), SlabBoundarySecondMomentUpper j B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n c : ℕ, 1 ≤ n → 5*c ≤ n →
      ∀ x w : Vertex (k+1),
      x ∈ sourceAnnulus n c → w ∈ sourceRD n c →
      3*(n : ℝ)/4 ≤ latticeDistance 0 x →
      (percolation (k+1) (criticalPoint (k+1))).real
        (connectionToSetEvent
          ((sourceAnnulus n c : Finset (Vertex (k+1))) : Set (Vertex (k+1))) x {w}) ≤
        K*(1+((n : ℝ)-latticeDistance 0 x))*(1+(sourceR c w : ℝ))*
          (n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ) := by
  let K₀ : ℝ := (2*C)*(10 : ℝ)^((k+1)-1)
  let K₂ : ℝ := (6*((k+1 : ℕ) : ℝ))*(4*C*(A+B)*(9 : ℝ)^((k+1)-1))*
    (2*C)*(10 : ℝ)^((k+1)-1)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  refine ⟨K₀+K₂+1,by linarith,?_⟩
  intro n c hn hcn x w hx hw hxouter
  have hd : 1 ≤ k+1 := by omega
  obtain ⟨hspos,hsc,i,hfaceN,htransN⟩ := sourceRD_face_chart hw
  have hrs : sourceR c w < sParam c w := (mem_sourceRD.mp hw).2
  have hwAnn : w ∈ sourceAnnulus n c := (Finset.mem_filter.mp hw).1
  have hxQ : x ∈ heartAnnulus (centeredBox (k+1) n) (centeredBox (k+1) c) := by
    simpa only [sourceAnnulus_eq_heartAnnulus] using hx
  have hwQ : w ∈ heartAnnulus (centeredBox (k+1) n) (centeredBox (k+1) c) := by
    simpa only [sourceAnnulus_eq_heartAnnulus] using hwAnn
  have hxdepth : 0 ≤ (n : ℝ)-latticeDistance 0 x := by
    obtain ⟨j,wall,positive,hhalf,hdepth⟩ := cube_nearest_coordinate_halfSpace hd x
      (heartAnnulus_subset _ _ hxQ)
    have hh : 0 ≤ coordinateDepth j wall positive x := hhalf (heartAnnulus_subset _ _ hxQ)
    rwa [hdepth] at hh
  let T : ℝ := (1+((n : ℝ)-latticeDistance 0 x))*(1+(sourceR c w : ℝ))*
    (n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  rw [sourceAnnulus_eq_heartAnnulus]
  change _ ≤ (K₀+K₂+1)*(1+((n : ℝ)-latticeDistance 0 x))*
    (1+(sourceR c w : ℝ))*(n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ)
  have hfinish (K : ℝ) (hK : K ≤ K₀+K₂+1)
      (hp : (percolation (k+1) (criticalPoint (k+1))).real
        (connectionToSetEvent
          (heartAnnulus (centeredBox (k+1) n) (centeredBox (k+1) c) : Set (Vertex (k+1)))
          x {w}) ≤ K*T) :
      (percolation (k+1) (criticalPoint (k+1))).real
        (connectionToSetEvent
          (heartAnnulus (centeredBox (k+1) n) (centeredBox (k+1) c) : Set (Vertex (k+1)))
          x {w}) ≤ (K₀+K₂+1)*(1+((n : ℝ)-latticeDistance 0 x))*
          (1+(sourceR c w : ℝ))*(n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ) := by
    calc
      _ ≤ K*T := hp
      _ ≤ (K₀+K₂+1)*T := mul_le_mul_of_nonneg_right hK hT
      _ = _ := by dsimp [T]; ring
  by_cases hs : 2 ≤ sParam c w
  · have hface : |w i| = (c : ℤ)+(sourceR c w : ℤ) := by
      rw [← Int.natCast_natAbs,hfaceN,Nat.cast_add]
    have htrans : ∀ j : Fin (k+1), j ≠ i →
        |w j| ≤ (c : ℤ)-(sParam c w : ℤ) := by
      intro j hji
      have hh : |w j| ≤ ((c-sParam c w : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast htransN j hji
      simpa only [Nat.cast_sub hsc] using hh
    apply hfinish K₂ (by linarith)
    by_cases hsign : 0 ≤ w i
    · have hp := positive_RD_connection_le hd hn hs hrs hsc hcn C A B hC hA hB
        panis arm second x w i hxQ hwQ hxouter
        (by simpa only [abs_of_nonneg hsign] using hface) htrans
      calc
        _ ≤ _ := hp
        _ = K₂*T := by dsimp [K₂,T]; ring
    · have hnegface : (-w) i = (c : ℤ)+(sourceR c w : ℤ) := by
        simp only [Pi.neg_apply]
        rw [abs_of_nonpos (by omega)] at hface
        exact hface
      have hnegtrans : ∀ j : Fin (k+1), j ≠ i →
          |(-w) j| ≤ (c : ℤ)-(sParam c w : ℤ) := by
        intro j hj
        simpa only [Pi.neg_apply,abs_neg] using htrans j hj
      have hp := positive_RD_connection_le hd hn hs hrs hsc hcn C A B hC hA hB
        panis arm second (-x) (-w) i ((neg_mem_heartAnnulus x).mpr hxQ)
        ((neg_mem_heartAnnulus w).mpr hwQ)
        (by simpa only [distance_zero_neg] using hxouter) hnegface hnegtrans
      rw [annulus_connection_probability_inversion,distance_zero_neg] at hp
      calc
        _ ≤ _ := hp
        _ = K₂*T := by dsimp [K₂,T]; ring
  · have hsone : sParam c w = 1 := by omega
    have hrzero : sourceR c w = 0 := by omega
    have hnorm : linfDist (0 : Vertex (k+1)) w = c := by
      have hbase := (mem_sourceRD.mp hw).1.2
      unfold sourceR at hrzero
      omega
    have hwinner : latticeDistance 0 w ≤ 2*(c : ℝ) := by
      rw [← linfDist_cast_eq_latticeDistance,hnorm]
      linarith [show (0 : ℝ) ≤ (c : ℝ) from Nat.cast_nonneg c]
    have hp := annulus_inner_connection_le hd hn hcn C hC panis x w hxQ hwQ hxouter hwinner
    apply hfinish K₀ (by linarith)
    calc
      _ ≤ _ := hp
      _ = K₀*T := by dsimp [K₀,T]; rw [hsone,hrzero]; simp; ring

end NearCritical.Section8
