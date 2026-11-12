module

public import NearCritical.CriticalTwoPointBounds
public import Mathlib.Algebra.Module.ZLattice.Summable

/-! Euclidean power summability on the project's actual integer vertices.
The auxiliary real function space carries its supremum norm; the comparison
with the explicitly defined Euclidean norm is proved below. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- The coordinatewise real embedding of the existing integer vertices. -/
def vertexReal {d : ℕ} (x : Vertex d) : Fin d → ℝ := fun i => (x i : ℝ)

lemma vertexReal_injective (d : ℕ) : Function.Injective (@vertexReal d) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (x i : ℝ) = (y i : ℝ) at hi
  exact_mod_cast hi

lemma vertexReal_norm_le_euclideanNorm {d : ℕ} (x : Vertex d) :
    ‖vertexReal x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)).mpr
  intro i
  change |(x i : ℝ)| ≤ Real.sqrt (∑ j, (x j : ℝ) ^ 2)
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j : ℝ)) (Finset.mem_univ i))

private abbrev integerSpan (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

private def vertexInSpan {d : ℕ} (x : Vertex d) : integerSpan d := by
  refine ⟨vertexReal x, ?_⟩
  apply ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨x i, by simp [vertexReal]⟩

private lemma vertexInSpan_injective (d : ℕ) : Function.Injective (@vertexInSpan d) := by
  intro x y h
  exact vertexReal_injective d (congrArg Subtype.val h)

/-- Integer-lattice power convergence with no summability premise. At the
origin, Mathlib's negative real power of zero is zero. -/
theorem summable_euclideanNorm_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable (fun x : Vertex d => euclideanNorm x ^ r) := by
  have hrank : Module.finrank ℤ (integerSpan d) = d := by
    rw [ZLattice.rank ℝ (integerSpan d)]
    simp
  have hs := ZLattice.summable_norm_rpow (integerSpan d) r (by simpa [hrank] using hr)
  have hcomp := hs.comp_injective (vertexInSpan_injective d)
  change Summable (fun x : Vertex d => ‖vertexReal x‖ ^ r) at hcomp
  have hrneg : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg d))
  apply hcomp.of_nonneg_of_le (fun x => Real.rpow_nonneg (euclideanNorm_nonneg x) r)
  intro x
  by_cases hx : x = 0
  · subst x
    have he0 : euclideanNorm (0 : Vertex d) = 0 := by simp [euclideanNorm]
    rw [he0, Real.zero_rpow hrneg.ne]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have hxreal : vertexReal x ≠ 0 := by
      intro h
      apply hx
      funext i
      have hi := congrFun h i
      change (x i : ℝ) = 0 at hi
      exact_mod_cast hi
    exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hxreal)
      (vertexReal_norm_le_euclideanNorm x) hrneg.le

/-- Regularizing the origin and small radii preserves summability. -/
theorem summable_regularized_euclideanNorm_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable (fun x : Vertex d => (max 1 (euclideanNorm x)) ^ r) := by
  classical
  have hs := (summable_euclideanNorm_rpow d r hr).update (0 : Vertex d) 1
  have hrneg : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg d))
  apply hs.of_nonneg_of_le (fun x => Real.rpow_nonneg (by positivity) r)
  intro x
  by_cases hx : x = 0
  · subst x
    simp [euclideanNorm]
  · rw [Function.update_of_ne hx]
    exact Real.rpow_le_rpow_of_nonpos (euclideanNorm_pos hx) (le_max_right _ _) hrneg.le

end NearCritical
