module
public import NearCritical.WaterCubeFaceArms
public import NearCritical.HalfSpaceOneArmExtension

/-! Quantitative eq.onearm_up comparisons for actual cube faces, from the
proved NEW half-space extension and its named STANDARD inputs. The required
starting-depth condition remains explicit, including endpoint shifts. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Depth measured from the face OPPOSITE the target face. -/
def waterCubeOppositeDepth {d : ℕ} (i : Fin d) (r : ℕ)
    (upper : Bool) (x : Vertex d) : ℕ :=
  if upper then (x i + (r : ℤ)).toNat else ((r : ℤ) + 1 - x i).toNat

def waterCubeFaceConnectionEvent {d : ℕ} (i : Fin d) (r R : ℕ) (upper : Bool)
    (x : DomainVertex (waterCube d i r R)) : Set (Configuration d) :=
  latticeBoundaryConnectionEvent (waterCube d i r R) x
    (if upper then positiveFace _ i else negativeFace _ i)

lemma waterCube_face_probability_le_halfSpace {d : ℕ} (p : unitInterval)
    (i : Fin d) (r R : ℕ) (upper : Bool) (x : DomainVertex (waterCube d i r R)) :
    percolation d p (waterCubeFaceConnectionEvent i r R upper x) ≤
      percolation d p (halfSpaceArmEvent i
        (waterCubeOppositeDepth i r upper x.val) (2 * r + 1)) := by
  cases upper
  · exact waterCube_negativeFace_probability_le_halfSpace p i r R x
  · exact waterCube_positiveFace_probability_le_halfSpace p i r R x

/-- Same constants for BOTH actual target faces, fixed before p,r,R,x.
This discharges finite-face vs half-space probability comparison; applying it
to every issued endpoint in the product sum still requires depth bookkeeping. -/
theorem waterCube_face_bounds_of_standard_inputs {d : ℕ} (i : Fin d)
    {E A B b : ℝ} (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (p : unitInterval) (r R : ℕ) (upper : Bool)
      (x : DomainVertex (waterCube d i r R)),
      2 * waterCubeOppositeDepth i r upper x.val ≤ 2 * r + 1 →
      ((criticalPoint d : ℝ) < (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ) + (((2 * r + 1 : ℕ) : ℝ) ^ 2)⁻¹ →
        (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
          C * ((waterCubeOppositeDepth i r upper x.val + 1 : ℝ) /
            ((2 * r + 1 : ℕ) : ℝ) ^ 3)) ∧
      (p ≤ criticalPoint d →
        (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
          C * ((waterCubeOppositeDepth i r upper x.val + 1 : ℝ) /
            ((2 * r + 1 : ℕ) : ℝ) ^ 3) *
              Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (2 * r + 1 : ℕ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := halfSpace_onearm_extension_of_standard_inputs i
    hE hA hB hb hpc hpc1 criticalArm pioneers entropic
  refine ⟨C, c, hC, hc, ?_⟩
  intro p r R upper x hdepth
  have h := hbound p (waterCubeOppositeDepth i r upper x.val) (2 * r + 1)
    (by omega) hdepth
  have hle := ENNReal.toReal_mono (measure_ne_top (percolation d p) _)
    (waterCube_face_probability_le_halfSpace p i r R upper x)
  exact ⟨fun hp hw => hle.trans (h.1 hp hw), fun hp => hle.trans (h.2 hp)⟩

end NearCritical
