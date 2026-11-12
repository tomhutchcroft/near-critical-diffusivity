module

public import NearCritical.Section10StepDiameter
public import NearCritical.PreGoodUpperCount

/-! Cardinalities entering the diameter bound of a lattice step.

* `orientedLatticePairs_card_le`: at most `2 d |S|` oriented pairs in `S`.
* `stepMid_card_le`: the middle region has at most `(6 t + 1)^d` vertices.
* `NestLayout.srcBoundary_card_le`: the source boundary of a `k`-nest of typical
  clusters has at most `k C_b (2t)^2` points.
* `NestLayout.tgtBoundary_card_le`: the target boundary of a pre-good cube has
  at most `C (2t)^(d-6) * 2 C_b (2t)^2` points.

These are `|E| <~ n^d`, `|A| <~ n^2`, `|B| <~ n^(d-4)` of lem.sprinkling.AB.geo
for the actual step.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem orientedLatticePairs_card_le {d : ℕ} (S : Finset (Vertex d)) :
    (orientedLatticePairs S).card ≤ S.card * (2 * d) := by
  have hsub : orientedLatticePairs S ⊆
      (S ×ˢ (Finset.univ : Finset (Fin d × Bool))).image (fun p : Vertex d × (Fin d × Bool) =>
        (p.1, if p.2.2 then Function.update p.1 p.2.1 (p.1 p.2.1 + 1)
          else Function.update p.1 p.2.1 (p.1 p.2.1 - 1))) := by
    intro e he
    obtain ⟨e1, e2⟩ := e
    obtain ⟨h1, _, hadj⟩ := (mem_orientedLatticePairs S e1 e2).mp he
    obtain ⟨b, _, hb | hb⟩ := hadj
    · refine Finset.mem_image.mpr ⟨(e1, (b.2, true)), Finset.mem_product.mpr
        ⟨h1, Finset.mem_univ _⟩, ?_⟩
      obtain ⟨hb1, hb2⟩ := hb
      simp only [if_true]
      rw [hb2, hb1]
      rfl
    · refine Finset.mem_image.mpr ⟨(e1, (b.2, false)), Finset.mem_product.mpr
        ⟨h1, Finset.mem_univ _⟩, ?_⟩
      obtain ⟨hb1, hb2⟩ := hb
      have h2 : e2 = Function.update e1 b.2 (e1 b.2 - 1) := by
        rw [hb2, hb1]
        funext k
        unfold bondTip
        by_cases hk : k = b.2
        · subst hk
          simp
        · simp [Function.update_of_ne hk]
      simp only [Bool.false_eq_true, if_false]
      rw [h2]
  calc (orientedLatticePairs S).card
      ≤ (S ×ˢ (Finset.univ : Finset (Fin d × Bool))).card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
    _ = S.card * (2 * d) := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, mul_comm d 2]

theorem stepMid_card_le {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    (stepMid t c i).card ≤ (2 * (3 * t) + 1) ^ d := by
  unfold stepMid
  rw [card_translateSites]
  unfold section9FiniteMiddle section9FiniteTube
  exact (Finset.card_filter_le _ _).trans (le_of_eq (card_centeredBox_exact d (3 * t)))

variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.srcBoundary_card_le (G : Λ.Φ) (ℓ : RouteLabel D) (pl : Bool)
    (nest : Finset (Finset (Vertex d))) (hnest : nest ⊆ Λ.fam G ℓ.site) :
    ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ) ≤
      (nest.card : ℝ) * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2) := by
  have h1 : (sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card ≤
      ∑ C ∈ nest, (Λ.src G ℓ pl C).card := by
    unfold sprinklingTargetBoundary
    exact Finset.card_biUnion_le
  have h2 : ∀ C ∈ nest, ((Λ.src G ℓ pl C).card : ℝ) ≤
      Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2 := by
    intro C hC
    have htyp := ((mem_typicalClusterFamily _ _ _ _ C).mp (hnest hC)).2
    exact (htyp.2.2.2.2.2.1 (Λ.dir ℓ, true) pl).2
  calc ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ)
      ≤ ((∑ C ∈ nest, (Λ.src G ℓ pl C).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ C ∈ nest, ((Λ.src G ℓ pl C).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _C ∈ nest, Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2 := Finset.sum_le_sum h2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem NestLayout.tgtBoundary_card_le (G : Λ.Φ) (ℓ : RouteLabel D)
    (hgood : Λ.goodCube G ℓ.target) (hbU : 0 ≤ Λ.typ.boundaryUpper) :
    ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) ≤
      (Λ.typ.countUpper * (2 * (Λ.t : ℝ)) ^ (d - 6)) *
        (2 * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2)) := by
  have h1 : (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card ≤
      ∑ C ∈ Λ.fam G ℓ.target, (Λ.tgt G ℓ C).card := by
    unfold sprinklingTargetBoundary
    exact Finset.card_biUnion_le
  have h2 : ∀ C ∈ Λ.fam G ℓ.target, ((Λ.tgt G ℓ C).card : ℝ) ≤
      2 * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2) := by
    intro C hC
    have htyp := ((mem_typicalClusterFamily _ _ _ _ C).mp hC).2
    have ha := (htyp.2.2.2.2.2.1 (Λ.dir ℓ, false) true).2
    have hb := (htyp.2.2.2.2.2.1 (Λ.dir ℓ, false) false).2
    have hu : (Λ.tgt G ℓ C).card ≤
        (typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C
          (Λ.dir ℓ, false) true).card +
        (typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C
          (Λ.dir ℓ, false) false).card := Finset.card_union_le _ _
    have hu' := (Nat.cast_le (α := ℝ)).mpr hu
    push_cast at hu'
    linarith
  have hcount : ((Λ.fam G ℓ.target).card : ℝ) ≤
      Λ.typ.countUpper * (2 * (Λ.t : ℝ)) ^ (d - 6) := hgood.2
  have hpos : (0:ℝ) ≤ 2 * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2) := by positivity
  calc ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ)
      ≤ ((∑ C ∈ Λ.fam G ℓ.target, (Λ.tgt G ℓ C).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ C ∈ Λ.fam G ℓ.target, ((Λ.tgt G ℓ C).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _C ∈ Λ.fam G ℓ.target, 2 * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2) :=
        Finset.sum_le_sum h2
    _ = ((Λ.fam G ℓ.target).card : ℝ) * (2 * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hpos

end NearCritical.Section10
