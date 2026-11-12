module
public import NearCritical.HalfSpaceTranslation

/-! Single-coordinate reflection invariance of the actual lattice law. Reflecting
coordinate `k` maps the bond `(v, i)` for `i ≠ k` to `(refl v, i)`. For `i = k`
the endpoints swap, so the image bond has base `refl (v + e_k)`. Complements
`LatticeInversion` and `LatticePermutation`: the full hyperoctahedral symmetry of
the restricted connection law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set

/-- Reflect coordinate `k`: `x ↦ x` with `x k ↦ -x k`. -/
def reflVertex {d : ℕ} (k : Fin d) (x : Vertex d) : Vertex d :=
  Function.update x k (-x k)

@[simp] lemma reflVertex_reflVertex {d : ℕ} (k : Fin d) (x : Vertex d) :
    reflVertex k (reflVertex k x) = x := by
  funext j
  by_cases hj : j = k <;> simp [reflVertex,Function.update_apply,hj]

lemma reflVertex_injective {d : ℕ} (k : Fin d) : Function.Injective (reflVertex k) :=
  Function.LeftInverse.injective (reflVertex_reflVertex k)

/-- The induced bond map. -/
def reflBondFun {d : ℕ} (k : Fin d) (e : Bond d) : Bond d :=
  if e.2 = k then (reflVertex k (bondTip e),k) else (reflVertex k e.1,e.2)

/-- For a bond in direction `k`, the reflected bond's tip is the reflected base. -/
lemma bondTip_reflBond_eq {d : ℕ} (k : Fin d) (e : Bond d) (he : e.2 = k) :
    bondTip (reflVertex k (bondTip e),k) = reflVertex k e.1 := by
  funext j
  by_cases hj : j = k <;> simp [bondTip,reflVertex,Function.update_apply,hj,he] <;> ring

/-- For a bond transverse to `k`, reflection commutes with taking the tip. -/
lemma bondTip_reflBond_ne {d : ℕ} (k : Fin d) (e : Bond d) (he : e.2 ≠ k) :
    bondTip (reflVertex k e.1,e.2) = reflVertex k (bondTip e) := by
  funext j
  by_cases hj : j = k <;> by_cases hj2 : j = e.2 <;>
    simp [bondTip,reflVertex,Function.update_apply,hj,hj2,he,Ne.symm he] <;> ring

lemma reflBondFun_involutive {d : ℕ} (k : Fin d) (e : Bond d) :
    reflBondFun k (reflBondFun k e) = e := by
  by_cases he : e.2 = k
  · have h1 : reflBondFun k e = (reflVertex k (bondTip e),k) := by simp [reflBondFun,he]
    rw [h1]
    show (if k = k then (reflVertex k (bondTip (reflVertex k (bondTip e),k)),k)
      else (reflVertex k (reflVertex k (bondTip e)),k)) = e
    rw [if_pos rfl,bondTip_reflBond_eq k e he,reflVertex_reflVertex]
    exact Prod.ext rfl he.symm
  · have h1 : reflBondFun k e = (reflVertex k e.1,e.2) := by simp [reflBondFun,he]
    rw [h1]
    show (if e.2 = k then (reflVertex k (bondTip (reflVertex k e.1,e.2)),k)
      else (reflVertex k (reflVertex k e.1),e.2)) = e
    rw [if_neg he,reflVertex_reflVertex]

def reflBond {d : ℕ} (k : Fin d) : Bond d ≃ Bond d where
  toFun := reflBondFun k
  invFun := reflBondFun k
  left_inv := reflBondFun_involutive k
  right_inv := reflBondFun_involutive k

def reflConfiguration {d : ℕ} (k : Fin d) (ω : Configuration d) : Configuration d :=
  fun e => ω (reflBond k e)

lemma measurable_reflConfiguration {d : ℕ} (k : Fin d) :
    Measurable (reflConfiguration (d := d) k) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

theorem percolation_map_refl {d : ℕ} (k : Fin d) (p : unitInterval) :
    (percolation d p).map (reflConfiguration k) = percolation d p := by
  change (Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)).map
    (fun ω e => ω (reflBond k e)) = _
  simpa [percolation,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,
    Equiv.piCongrLeft',Equiv.symm_symm] using
    (Measure.infinitePi_map_piCongrLeft
      (fun _ : Bond d => bernoulliMeasure true false p) (reflBond k).symm)

/-- One direction of the adjacency correspondence, used twice by involutivity. -/
lemma openGraph_refl_adj_mp {d : ℕ} (k : Fin d) (ω : Configuration d) (x y : Vertex d)
    (h : (openGraph (reflConfiguration k ω)).Adj x y) :
    (openGraph ω).Adj (reflVertex k x) (reflVertex k y) := by
  obtain ⟨e,he,hxy⟩ := h
  have he' : ω (reflBondFun k e) = true := he
  by_cases hk : e.2 = k
  · have hb : reflBondFun k e = (reflVertex k (bondTip e),k) := by simp [reflBondFun,hk]
    rw [hb] at he'
    have ht := bondTip_reflBond_eq k e hk
    rcases hxy with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact ⟨_,he',Or.inr ⟨by rw [hy],by rw [ht,hx]⟩⟩
    · exact ⟨_,he',Or.inl ⟨by rw [hx],by rw [ht,hy]⟩⟩
  · have hb : reflBondFun k e = (reflVertex k e.1,e.2) := by simp [reflBondFun,hk]
    rw [hb] at he'
    have ht := bondTip_reflBond_ne k e hk
    rcases hxy with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact ⟨_,he',Or.inl ⟨by rw [hx],by rw [ht,hy]⟩⟩
    · exact ⟨_,he',Or.inr ⟨by rw [hy],by rw [ht,hx]⟩⟩

lemma reflConfiguration_reflConfiguration {d : ℕ} (k : Fin d) (ω : Configuration d) :
    reflConfiguration k (reflConfiguration k ω) = ω := by
  funext e
  change ω (reflBondFun k (reflBondFun k e)) = ω e
  rw [reflBondFun_involutive]

lemma openGraph_refl_adj {d : ℕ} (k : Fin d) (ω : Configuration d) (x y : Vertex d) :
    (openGraph (reflConfiguration k ω)).Adj x y ↔
      (openGraph ω).Adj (reflVertex k x) (reflVertex k y) := by
  constructor
  · exact openGraph_refl_adj_mp k ω x y
  · intro h
    have h2 := openGraph_refl_adj_mp k (reflConfiguration k ω) (reflVertex k x) (reflVertex k y)
      (by rwa [reflConfiguration_reflConfiguration])
    simpa using h2

def restrictedReflGraphIso {d : ℕ} (k : Fin d) (ω : Configuration d) (S : Set (Vertex d)) :
    restrictedGraph (reflConfiguration k ω) S ≃g restrictedGraph ω (reflVertex k '' S) where
  toEquiv := ⟨reflVertex k,reflVertex k,reflVertex_reflVertex k,reflVertex_reflVertex k⟩
  map_rel_iff' := by
    intro x y
    change ((openGraph ω).Adj (reflVertex k x) (reflVertex k y) ∧
        reflVertex k x ∈ reflVertex k '' S ∧ reflVertex k y ∈ reflVertex k '' S) ↔
      ((openGraph (reflConfiguration k ω)).Adj x y ∧ x ∈ S ∧ y ∈ S)
    rw [← openGraph_refl_adj,(reflVertex_injective k).mem_set_image,
      (reflVertex_injective k).mem_set_image]

lemma connectionToSetEvent_refl {d : ℕ} (k : Fin d) (x : Vertex d) (S B : Set (Vertex d)) :
    reflConfiguration k ⁻¹' connectionToSetEvent S x B =
      connectionToSetEvent (reflVertex k '' S) (reflVertex k x) (reflVertex k '' B) := by
  ext ω
  constructor
  · rintro ⟨hx,y,hy,hyS,hp⟩
    exact ⟨⟨x,hx,rfl⟩,reflVertex k y,⟨y,hy,rfl⟩,⟨y,hyS,rfl⟩,
      (restrictedReflGraphIso k ω S).reachable_iff.mpr hp⟩
  · rintro ⟨hx,z,⟨y,hy,rfl⟩,hyS,hp⟩
    exact ⟨(reflVertex_injective k).mem_set_image.mp hx,y,hy,
      (reflVertex_injective k).mem_set_image.mp hyS,
      (restrictedReflGraphIso k ω S).reachable_iff.mp hp⟩

/-- Restricted connection probabilities are invariant under reflecting one coordinate. -/
theorem connectionToSet_probability_refl {d : ℕ} (k : Fin d) (p : unitInterval)
    (x : Vertex d) (S B : Set (Vertex d)) :
    percolation d p (connectionToSetEvent (reflVertex k '' S) (reflVertex k x)
      (reflVertex k '' B)) = percolation d p (connectionToSetEvent S x B) := by
  rw [← connectionToSetEvent_refl,← Measure.map_apply
    (measurable_reflConfiguration k) (measurableSet_connectionToSetEvent S x B),
    percolation_map_refl]

end NearCritical
