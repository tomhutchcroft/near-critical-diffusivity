module

public import NearCritical.Section9SprinklingCluster
public import NearCritical.SprinklingIntrinsic

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Boundary sites outside the source patch whose singleton sprinkling
cluster meets the sprinkling cluster of that patch. -/
def bridgeCoalescingSites {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A sourceFace B : Finset (Vertex d)) : Finset (Vertex d) :=
  (sourceFace \ A).filter fun x =>
    (section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B ∩
      section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B).Nonempty

/-- The three checks of the source typical-bridge event, on the revealed
offspring, distinct coalescing sites, and boundary intrinsic diameter. -/
def IsTypicalSprinklingBridge {d : ℕ} {ι : Type*}
    (offspring : Finset ι) (coalescingSites : Finset (Vertex d))
    (diameter minOffspring maxOffspring maxCoalescing maxDiameter : ℕ) : Prop :=
  10 ≤ minOffspring ∧ minOffspring ≤ offspring.card ∧ offspring.card ≤ maxOffspring ∧
    coalescingSites.card ≤ maxCoalescing ∧ diameter ≤ maxDiameter

theorem IsTypicalSprinklingBridge.enough_offspring {d : ℕ} {ι : Type*}
    {offspring : Finset ι} {coalescingSites : Finset (Vertex d)}
    {diameter minOffspring maxOffspring maxCoalescing maxDiameter k : ℕ}
    (ht : IsTypicalSprinklingBridge offspring coalescingSites diameter
      minOffspring maxOffspring maxCoalescing maxDiameter) (hk : k ≤ minOffspring) :
    k ≤ offspring.card :=
  hk.trans ht.2.1

end NearCritical.Section10
