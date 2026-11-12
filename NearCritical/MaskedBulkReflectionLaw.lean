module

public import NearCritical.LatticeInversion
public import NearCritical.MaskedWaterCubeSlabLaw

/-! Reflection invariance of the actual bulk law. The affine map preserves
the strict bulk band; the issued graph itself need not be invariant. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set
open scoped Classical

theorem percolationProfile_map_inversion {d : ℕ} (ρ : Bond d → unitInterval) :
    (percolationProfile d ρ).map invertConfiguration =
      percolationProfile d (fun e => ρ (invertBond e)) := by
  change (Measure.infinitePi (fun e : Bond d => bernoulliMeasure true false (ρ e))).map
    (fun ω e => ω (invertBond e)) =
      Measure.infinitePi (fun e : Bond d => bernoulliMeasure true false (ρ (invertBond e)))
  simpa [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', Equiv.apply_symm_apply] using
    (Measure.infinitePi_map_piCongrLeft
      (fun e : Bond d => bernoulliMeasure true false (ρ (invertBond e))) invertBond.symm)

theorem waterCube_bulkVertices_reflection_iff {d : ℕ} (i : Fin d) (r R : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ) (x : Vertex d) :
    Pi.single i (1 : ℤ) - x ∈ bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ ↔
      x ∈ bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ := by
  let a : Vertex d := Pi.single i (1 : ℤ)
  let V := bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ
  have hm : 0 ≤ ⌊δ*(2*(r : ℝ)+1)/2⌋ := Int.floor_nonneg.mpr (by positivity)
  have hf (y : Vertex d) (hy : y ∈ V) : a-y ∈ V := by
    rcases (mem_bulkVertices_waterCube_iff_band i r R δ y).mp hy with ⟨hyU, hylo, hyhi⟩
    apply (mem_bulkVertices_waterCube_iff_band i r R δ (a-y)).mpr
    have hay : (a-y) i = 1-y i := by simp [a]
    refine ⟨?_, ?_⟩
    · apply mem_rectangularBox.mpr
      intro j
      by_cases hj : j = i
      · subst j
        simp only [ite_true, hay]
        omega
      · have hj' := (mem_rectangularBox.mp hyU) j
        simp only [hj, ite_false] at hj' ⊢
        have he : (a-y) j = -y j := by simp [a, hj]
        rw [he]
        omega
    · rw [hay]
      constructor <;> omega
  change a-x ∈ V ↔ x ∈ V
  exact ⟨fun h => by simpa only [sub_sub_cancel] using hf (a-x) h, hf x⟩

theorem waterCube_bulkMask_reflected_bond_iff {d : ℕ} (i : Fin d) (r R : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ) (e : Bond d) :
    translateBond (Pi.single i (1 : ℤ)) (invertBond e) ∈
      internalBondSet (bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) ↔
    e ∈ internalBondSet (bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) := by
  simp only [mem_internalBondSet, bondTip_translate]
  change (Pi.single i (1 : ℤ) + -bondTip e ∈ _ ∧
    Pi.single i (1 : ℤ) + bondTip (-bondTip e, e.2) ∈ _) ↔ _
  simp only [bondTip_neg_tip, ← sub_eq_add_neg,
    waterCube_bulkVertices_reflection_iff i r R δ hδ, and_comm]

/-- Translation followed by inversion on configurations pulls back the
profile by the affine reflection on bonds, which preserves the bulk mask. -/
theorem bulkPercolation_waterCube_map_reflection {d : ℕ} (i : Fin d) (r R : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ) (p q : unitInterval) :
    ((bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).map
      (translateConfiguration (Pi.single i (1 : ℤ)))).map invertConfiguration =
    bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q := by
  unfold bulkPercolation maskedPercolation
  rw [percolationProfile_map_translation, percolationProfile_map_inversion]
  congr 1
  funext e
  simp only [waterCube_bulkMask_reflected_bond_iff i r R δ hδ e]

/-- Full restricted-connection probabilities transform with the domain and
target under the same affine map. This assertion does not reflect a fixed
issued graph. -/
theorem bulkPercolation_waterCube_connection_reflection {d : ℕ}
    (i : Fin d) (r R : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (p q : unitInterval)
    (S A : Set (Vertex d)) (x : Vertex d) :
    let μ := bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q
    let f := fun y : Vertex d => Pi.single i (1 : ℤ) - y
    μ (connectionToSetEvent (f '' S) (f x) (f '' A)) = μ (connectionToSetEvent S x A) := by
  dsimp only
  let a : Vertex d := Pi.single i (1 : ℤ)
  let μ := bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q
  have h := congrArg (fun ν : Measure (Configuration d) => ν (connectionToSetEvent S x A))
    (bulkPercolation_waterCube_map_reflection i r R δ hδ p q)
  change ((μ.map (translateConfiguration a)).map invertConfiguration)
    (connectionToSetEvent S x A) = μ (connectionToSetEvent S x A) at h
  rw [Measure.map_apply measurable_invertConfiguration (measurableSet_connectionToSetEvent S x A),
    connectionToSetEvent_inversion,
    Measure.map_apply (measurable_translateConfiguration a)
      (measurableSet_connectionToSetEvent _ _ _),
    connectionToSetEvent_translation] at h
  simpa only [Set.image_image, Function.comp_apply, ← sub_eq_add_neg, a, μ] using h

end NearCritical
