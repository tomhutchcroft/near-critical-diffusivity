module

public import NearCritical.Section10TrailCurrent
public import NearCritical.LatticeFullConductivity

/-! Section10 lem.nw.path / eq.nw.flow: lift the actual internal lattice path
and its final exit bond into E+(U). No converse for all edges in U+ is used. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- An actual open bond with base in U is an issued positive edge. -/
theorem issued_positive_adj_of_open_bond {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (e : Bond d) (he : e.1 ∈ U) (hopen : ω e = true)
    (x y : DomainVertex U)
    (hends : (x.val = e.1 ∧ y.val = bondTip e) ∨ (y.val = e.1 ∧ x.val = bondTip e)) :
    ((issuedNetwork U).positiveGraph (domainWeights ω) Set.univ).Adj x y := by
  have hei : e ∈ issuedBondSet U := Finset.mem_product.mpr ⟨he,Finset.mem_univ _⟩
  have hxy : (openGraph ω).Adj x.val y.val := ⟨e,hopen,hends⟩
  refine ⟨(fun h => hxy.ne (congrArg Subtype.val h)),Set.mem_univ _,Set.mem_univ _,⟨e,hei⟩,?_,?_⟩
  · simp [domainWeights,issuedBond,hopen]
  · rcases hends with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact Or.inl ⟨Subtype.ext hx.symm,Subtype.ext hy.symm⟩
    · exact Or.inr ⟨Subtype.ext hy.symm,Subtype.ext hx.symm⟩

/-- Both endpoints in U ensure that the unique positive-coordinate bond base
lies in U. Merely requiring endpoints in U+ would be insufficient. -/
theorem issued_positive_adj_of_open_inside {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (x y : DomainVertex U) (hx : x.val ∈ U) (hy : y.val ∈ U)
    (hxy : (openGraph ω).Adj x.val y.val) :
    ((issuedNetwork U).positiveGraph (domainWeights ω) Set.univ).Adj x y := by
  obtain ⟨e,he,hends⟩ := hxy
  have hbase : e.1 ∈ U := by
    rcases hends with ⟨hx',_⟩ | ⟨hy',_⟩
    · simpa only [hx'] using hx
    · simpa only [hy'] using hy
  exact issued_positive_adj_of_open_bond U ω e hbase he x y hends

def internalIssuedVertex {d : ℕ} (U : Finset (Vertex d)) (x : ↥(U : Set (Vertex d))) :
    DomainVertex U := ⟨x.val,base_mem_sitesPlus x.property⟩

def issuedInternalGraphHom {d : ℕ} (U : Finset (Vertex d)) (ω : Configuration d) :
    (openGraph ω).induce (U : Set (Vertex d)) →g
      (issuedNetwork U).positiveGraph (domainWeights ω) Set.univ where
  toFun := internalIssuedVertex U
  map_rel' := by
    intro x y hxy
    exact issued_positive_adj_of_open_inside U ω (internalIssuedVertex U x)
      (internalIssuedVertex U y) x.property y.property hxy

def issuedExitVertex {d : ℕ} (U : Finset (Vertex d)) (y : ↥(U : Set (Vertex d))) (i : Fin d) :
    DomainVertex U := ⟨bondTip (y.val,i),tip_mem_sitesPlus y.property i⟩

/-- Actual internal open walk plus final open exit carries a supported unit
current with derived path-indicator and energy bounds in the issued network. -/
theorem issued_internal_walk_exit_current {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (S T : Set (DomainVertex U)) (hST : Disjoint S T)
    (x y : ↥(U : Set (Vertex d))) (i : Fin d)
    (hx : internalIssuedVertex U x ∈ S) (hz : issuedExitVertex U y i ∈ T)
    (w : ((openGraph ω).induce (U : Set (Vertex d))).Walk x y)
    (hexit : ω (y.val,i) = true) :
    ∃ (P : Finset (IssuedBond U)) (θ : IssuedBond U → ℝ),
      (issuedNetwork U).IsBoundaryUnitFlow S T θ ∧ Network.FlowSupported (domainWeights ω) θ ∧
      (∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0) ∧
      (∀ e ∈ P, (domainWeights ω : IssuedBond U → ℝ) e = 1) ∧
      P.card ≤ w.length+1 ∧ Network.flowEnergy (domainWeights ω) θ ≤ (w.length+1:ℕ) := by
  let φ := issuedInternalGraphHom U ω
  have hadj : ((issuedNetwork U).positiveGraph (domainWeights ω) Set.univ).Adj
      (φ y) (issuedExitVertex U y i) :=
    issued_positive_adj_of_open_bond U ω (y.val,i) y.property hexit _ _ (Or.inl ⟨rfl,rfl⟩)
  let v := (w.map φ).concat hadj
  have ha (e : IssuedBond U) : (domainWeights ω : IssuedBond U → ℝ) e = 0 ∨
      (domainWeights ω : IssuedBond U → ℝ) e = 1 := by
    cases he : ω e.val <;> simp [domainWeights,issuedBond,he]
  obtain ⟨P,θ,hunit,hsupp,hmag,hopen,hcard,henergy⟩ :=
    Network.positive_trail_boundary_current_energy (issuedNetwork U) (domainWeights ω)
      ha S T hST hx hz v.bypass v.bypass_isPath.isTrail
  have hlen : v.bypass.length ≤ w.length+1 := by
    calc
      _ ≤ v.length := v.length_bypass_le_length
      _ = _ := by simp only [v,SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_map]
  have hmag' (e : IssuedBond U) : |θ e| ≤ if e ∈ P then (1:ℝ) else 0 := by
    have h := hmag e
    by_cases he : e ∈ P
    · rw [if_pos he] at h ⊢
      exact h
    · rw [if_neg he] at h ⊢
      exact h
  refine ⟨P,θ,hunit,hsupp,hmag',hopen,hcard.trans hlen,henergy.trans ?_⟩
  exact_mod_cast hlen

end NearCritical.Section10
