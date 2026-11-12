module
public import NearCritical.HalfSpaceTranslation

/-! Coordinate-permutation invariance of the actual lattice law, used for the
rotation step eq.boundaryCrossingRotation in lem.boundary_regularity
(main.tex ~6305) and for the source's "symmetry of Q among the directions"
arguments. A permutation `σ` of coordinates maps the positive-direction bond
`(v, i)` to the positive-direction bond `(σ·v, σ i)`, so no endpoint reversal
occurs (contrast with `LatticeInversion`). -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set

/-- Coordinate permutation of a vertex: `(permVertex σ x) j = x (σ⁻¹ j)`. -/
def permVertex {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Vertex d) : Vertex d :=
  fun j => x (σ.symm j)

lemma permVertex_symm_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Vertex d) :
    permVertex σ.symm (permVertex σ x) = x := by
  funext j
  simp [permVertex]

lemma permVertex_apply_symm {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Vertex d) :
    permVertex σ (permVertex σ.symm x) = x := by
  funext j
  simp [permVertex]

lemma permVertex_injective {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Function.Injective (permVertex σ) :=
  Function.LeftInverse.injective (permVertex_symm_apply σ)

lemma permVertex_bondTip {d : ℕ} (σ : Equiv.Perm (Fin d)) (e : Bond d) :
    permVertex σ (bondTip e) = bondTip (permVertex σ e.1, σ e.2) := by
  funext j
  simp only [permVertex,bondTip,Function.update_apply]
  by_cases h : j = σ e.2
  · subst h
    simp
  · have h' : σ.symm j ≠ e.2 := by
      intro h''
      apply h
      rw [← h'']
      simp
    simp [h,h']

/-- The induced bijection of positive-direction bonds. -/
def permBond {d : ℕ} (σ : Equiv.Perm (Fin d)) : Bond d ≃ Bond d where
  toFun e := (permVertex σ e.1, σ e.2)
  invFun e := (permVertex σ.symm e.1, σ.symm e.2)
  left_inv e := by simp [permVertex_symm_apply]
  right_inv e := by simp [permVertex_apply_symm]

def permConfiguration {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Configuration d) :
    Configuration d :=
  fun e => ω (permBond σ e)

lemma measurable_permConfiguration {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Measurable (permConfiguration (d := d) σ) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

/-- The product Bernoulli law is invariant under coordinate permutations. -/
theorem percolation_map_perm {d : ℕ} (σ : Equiv.Perm (Fin d)) (p : unitInterval) :
    (percolation d p).map (permConfiguration σ) = percolation d p := by
  change (Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)).map
    (fun ω e => ω (permBond σ e)) = _
  simpa [percolation,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,
    Equiv.piCongrLeft',Equiv.symm_symm] using
    (Measure.infinitePi_map_piCongrLeft
      (fun _ : Bond d => bernoulliMeasure true false p) (permBond σ).symm)

lemma openGraph_perm_adj {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (permConfiguration σ ω)).Adj x y ↔
      (openGraph ω).Adj (permVertex σ x) (permVertex σ y) := by
  constructor
  · rintro ⟨e,he,h | h⟩
    · exact ⟨permBond σ e,he,Or.inl ⟨by simp [h.1,permBond],
        by simp [h.2,permBond,permVertex_bondTip]⟩⟩
    · exact ⟨permBond σ e,he,Or.inr ⟨by simp [h.1,permBond],
        by simp [h.2,permBond,permVertex_bondTip]⟩⟩
  · rintro ⟨e,he,h | h⟩
    · have hx := congrArg (permVertex σ.symm) h.1
      rw [permVertex_symm_apply] at hx
      have hy := congrArg (permVertex σ.symm) h.2
      rw [permVertex_symm_apply,permVertex_bondTip] at hy
      refine ⟨(permBond σ).symm e,?_,Or.inl ⟨by simp [permBond,hx],by simp [permBond,hy]⟩⟩
      simpa [permConfiguration] using he
    · have hx := congrArg (permVertex σ.symm) h.1
      rw [permVertex_symm_apply] at hx
      have hy := congrArg (permVertex σ.symm) h.2
      rw [permVertex_symm_apply,permVertex_bondTip] at hy
      refine ⟨(permBond σ).symm e,?_,Or.inr ⟨by simp [permBond,hx],by simp [permBond,hy]⟩⟩
      simpa [permConfiguration] using he

def restrictedPermGraphIso {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Configuration d)
    (S : Set (Vertex d)) :
    restrictedGraph (permConfiguration σ ω) S ≃g restrictedGraph ω (permVertex σ '' S) where
  toEquiv := ⟨permVertex σ,permVertex σ.symm,permVertex_symm_apply σ,permVertex_apply_symm σ⟩
  map_rel_iff' := by
    intro x y
    change ((openGraph ω).Adj (permVertex σ x) (permVertex σ y) ∧
        permVertex σ x ∈ permVertex σ '' S ∧ permVertex σ y ∈ permVertex σ '' S) ↔
      ((openGraph (permConfiguration σ ω)).Adj x y ∧ x ∈ S ∧ y ∈ S)
    rw [← openGraph_perm_adj,(permVertex_injective σ).mem_set_image,
      (permVertex_injective σ).mem_set_image]

lemma connectionToSetEvent_perm {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Vertex d)
    (S B : Set (Vertex d)) :
    permConfiguration σ ⁻¹' connectionToSetEvent S x B =
      connectionToSetEvent (permVertex σ '' S) (permVertex σ x) (permVertex σ '' B) := by
  ext ω
  constructor
  · rintro ⟨hx,y,hy,hyS,hp⟩
    exact ⟨⟨x,hx,rfl⟩,permVertex σ y,⟨y,hy,rfl⟩,⟨y,hyS,rfl⟩,
      (restrictedPermGraphIso σ ω S).reachable_iff.mpr hp⟩
  · rintro ⟨hx,z,⟨y,hy,rfl⟩,hyS,hp⟩
    exact ⟨(permVertex_injective σ).mem_set_image.mp hx,y,hy,
      (permVertex_injective σ).mem_set_image.mp hyS,
      (restrictedPermGraphIso σ ω S).reachable_iff.mp hp⟩

/-- Restricted connection probabilities are invariant under coordinate permutations. -/
theorem connectionToSet_probability_perm {d : ℕ} (σ : Equiv.Perm (Fin d)) (p : unitInterval)
    (x : Vertex d) (S B : Set (Vertex d)) :
    percolation d p (connectionToSetEvent (permVertex σ '' S) (permVertex σ x)
      (permVertex σ '' B)) = percolation d p (connectionToSetEvent S x B) := by
  rw [← connectionToSetEvent_perm,← Measure.map_apply
    (measurable_permConfiguration σ) (measurableSet_connectionToSetEvent S x B),
    percolation_map_perm]

end NearCritical
