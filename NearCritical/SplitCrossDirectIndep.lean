module

public import NearCritical.NestFreshTube
public import NearCritical.SplitCrossDirectDistinctLower

/-! Independence of events on disjoint bond sets (item C of the direct proof
of `SplitCrossInput`).

* `DependsOn E S`: the event `E` is determined by the bonds of the finite set
  `S` (two configurations agreeing on `S` are both in or both out).
* `indep_of_dependsOn`: events depending on disjoint finite bond sets are
  independent under `percolation d p`.
* `restrictedGraph_eq_of_agree`: the restricted graph of a finite vertex domain
  `U` is determined by `internalBondSet U`; hence `finiteBoxCluster`,
  restricted connections with `T ⊆ U`, and `distinctLoc U L` (for local events
  determined by `internalBondSet U`) depend only on `internalBondSet U`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

/-- `E` is determined by the bonds in `S`. -/
def DependsOn (E : Set (Configuration d)) (S : Finset (Bond d)) : Prop :=
  ∀ ω ω' : Configuration d, (∀ e ∈ S, ω e = ω' e) → ω ∈ E → ω' ∈ E

lemma DependsOn.eq_preimage {E : Set (Configuration d)} {S : Finset (Bond d)}
    (h : DependsOn E S) :
    E = S.restrict ⁻¹' {ξ | extendConfiguration S (fun _ => false) ξ ∈ E} := by
  ext ω
  have hagree : ∀ e ∈ S, ω e = extendConfiguration S (fun _ => false) (S.restrict ω) e := by
    intro e he
    simp [extendConfiguration, he, Finset.restrict]
  exact ⟨fun hω => h ω _ hagree hω, fun hω => h _ ω (fun e he => (hagree e he).symm) hω⟩

lemma DependsOn.measurableSet {E : Set (Configuration d)} {S : Finset (Bond d)}
    (h : DependsOn E S) : MeasurableSet E := by
  rw [h.eq_preimage]
  exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict S)

lemma DependsOn.inter {E F : Set (Configuration d)} {S : Finset (Bond d)}
    (hE : DependsOn E S) (hF : DependsOn F S) : DependsOn (E ∩ F) S :=
  fun ω ω' h hω => ⟨hE ω ω' h hω.1, hF ω ω' h hω.2⟩

lemma DependsOn.mono {E : Set (Configuration d)} {S S' : Finset (Bond d)}
    (hE : DependsOn E S) (hS : S ⊆ S') : DependsOn E S' :=
  fun ω ω' h hω => hE ω ω' (fun e he => h e (hS he)) hω

/-- **Independence on disjoint bond sets.** -/
theorem indep_of_dependsOn (p : unitInterval) {E F : Set (Configuration d)}
    {S T : Finset (Bond d)} (hd : Disjoint S T) (hE : DependsOn E S) (hF : DependsOn F T) :
    (percolation d p).real (E ∩ F) = (percolation d p).real E * (percolation d p).real F := by
  have hi : IndepFun (S.restrict : Configuration d → (S → Bool))
      (T.restrict : Configuration d → (T → Bool)) (percolation d p) :=
    iIndepFun.indepFun_finset S T hd
      (iIndepFun_infinitePi (fun _ : Bond d => (measurable_id : Measurable (id : Bool → Bool))))
      (fun e => measurable_pi_apply e)
  have h := (indepFun_iff_measure_inter_preimage_eq_mul.mp hi)
    {ξ | extendConfiguration S (fun _ => false) ξ ∈ E}
    {ξ | extendConfiguration T (fun _ => false) ξ ∈ F}
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  rw [← hE.eq_preimage, ← hF.eq_preimage] at h
  rw [measureReal_def, h, ENNReal.toReal_mul]
  rfl

/-- The restricted graph of `U` reads only the internal bonds of `U`. -/
lemma restrictedGraph_eq_of_agree (U : Finset (Vertex d)) {ω ω' : Configuration d}
    (h : ∀ e ∈ internalBondSet U, ω e = ω' e) :
    restrictedGraph ω (U : Set (Vertex d)) = restrictedGraph ω' (U : Set (Vertex d)) := by
  have key : ∀ {η η' : Configuration d}, (∀ e ∈ internalBondSet U, η e = η' e) →
      ∀ x y, (restrictedGraph η (U : Set (Vertex d))).Adj x y →
        (restrictedGraph η' (U : Set (Vertex d))).Adj x y := by
    rintro η η' hagree x y ⟨⟨e, he, hends⟩, hx, hy⟩
    have hmem : e ∈ internalBondSet U := by
      rw [mem_internalBondSet]
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ Finset.mem_coe.mp hx, h2 ▸ Finset.mem_coe.mp hy⟩
      · exact ⟨h1 ▸ Finset.mem_coe.mp hy, h2 ▸ Finset.mem_coe.mp hx⟩
    exact ⟨⟨e, (hagree e hmem) ▸ he, hends⟩, hx, hy⟩
  ext x y
  exact ⟨key h x y, key (fun e he => (h e he).symm) x y⟩

lemma finiteBoxCluster_eq_of_agree (U : Finset (Vertex d)) {ω ω' : Configuration d}
    (h : ∀ e ∈ internalBondSet U, ω e = ω' e) (r : Vertex d) :
    finiteBoxCluster ω U r = finiteBoxCluster ω' U r := by
  ext x
  rw [mem_finiteBoxCluster, mem_finiteBoxCluster, restrictedGraph_eq_of_agree U h]

/-- A restricted connection inside `U` depends only on the internal bonds of `U`. -/
lemma conn_dependsOn (U : Finset (Vertex d)) {T : Set (Vertex d)}
    (hT : T ⊆ (U : Set (Vertex d))) (a b : Vertex d) :
    DependsOn (connectionToSetEvent T a {b}) (internalBondSet U) := by
  rintro ω ω' h ⟨haT, y, hy, hyT, ⟨π⟩⟩
  refine ⟨haT, y, hy, hyT, ?_⟩
  refine reachable_of_walk_good (fun _ => True) ?_ π (fun _ _ => trivial)
  intro e he1 he2 _ _ heo
  rw [← h e ((mem_internalBondSet U e).mpr ⟨hT he1, hT he2⟩)]
  exact heo

/-- The distinct-cluster event of tube edges depends only on the internal bonds. -/
theorem distinctLoc_dependsOn (U : Finset (Vertex d)) (es : List (TEdge d U)) :
    DependsOn (distinctLoc U (es.map TEdge.loc)) (internalBondSet U) := by
  rintro ω ω' h ⟨hall, hpair⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact conn_dependsOn U e.hT e.a e.b ω ω' h (hall _ hx)
  · refine hpair.imp (fun {x y} hxy => ?_)
    rw [← finiteBoxCluster_eq_of_agree U h, ← finiteBoxCluster_eq_of_agree U h]
    exact hxy

end NearCritical.SplitCrossDirect
end
